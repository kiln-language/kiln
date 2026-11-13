// Rebuilding the program so that a function can grow, which is what inlining needs.
//
// The instruction list is one flat vector that each `IRFunc` names a run in, and temps are
// numbered program-wide with every function owning a contiguous range, so until now nothing could
// insert an instruction. This copies each function into a fresh image, renumbering as it goes.
#include <{ir, opt}>
#include <parse::{types, upstream}>
#include <support::compiler>
#include <stdlib::{fmt, map, mem, option, string, vec}>

// How big a body may be and still be worth copying into its callers. `Vec.at` (the bounds check,
// the element address and the load) is twenty-two, and it is the one that matters.
local MAX_INLINE_INSTRS: long = 24;

// A body called from exactly one place is copied there up to this size: nothing is duplicated, and
// the bound keeps one caller from growing past what `flow.k` and the allocator handle well.
local MAX_SINGLE_INSTRS: long = 160;

// How deep a spliced body's own calls are spliced in turn.
local MAX_INLINE_DEPTH: long = 4;

// A caller grows by bodies taken for their one call site only up to this size: past it, the
// dataflow in `flow.k` costs more than the calls it saves.
local MAX_SINGLE_CALLER: long = 1000;

// A `--lib` build (main.k sets it): every `pub` function is emitted whatever calls it.
pub var gInlineLibrary: bool = false;

pub struct Relayout {
    code: Vec<Instr>,
    kinds: Vec<Lit>, structs: Vec<Sym>, pointees: Vec<Sym>,
    args: Vec<Temp>,
    aKinds: Vec<AsmKind>, aRegs: Vec<Sym>, aNames: Vec<Sym>,
    aVals: Vec<Temp>, aText: Vec<Sym>, aSizes: Vec<long>,

    // Old temp -> new temp, or NO_TEMP for one not met yet. One table for the whole program
    // rather than one per function: a temp belongs to exactly one function, so nothing collides
    // and nothing has to be cleared between them.
    tmap: Vec<Temp>,

    // ─── inlining ────────────────────────────────────────────────────────────
    fnOf: HashMap<str, long>,     // function name -> its index, for finding a call's target
    canInline: Vec<bool>,         // per function, decided once by `inlinableBody`
    // Every function's runs as they were. `p.funcs` is rewritten in place as each one is copied,
    // so by the time a later caller wants a callee's body, the entry for it already names the
    // new image while the body still has to be read out of the old one.
    orig: Vec<IRFunc>,
    // A spliced body's temps are fresh at every site, so they cannot share `tmap`, which is keyed
    // by the old id for the whole program. Stamped rather than cleared: clearing a table the size
    // of the program once per call site is exactly the cost this pass exists to avoid.
    smap: Vec<Temp>, smapGen: Vec<long>, spliceSeq: long,
    lmap: HashMap<str, Sym>,      // a spliced body's labels, renamed per site
    // A spliced body's by-value aggregate parameters: the caller's address, per splice (`aggSeq`).
    aggName: Vec<Sym>, aggTemp: Vec<Temp>, aggSeq: Vec<long>,
    labelSeq: long,
    // The splice being copied (its stamp and its label number), and the functions whose bodies
    // are being copied, outermost first: a call inside a spliced body is spliced in turn, never
    // into itself and never past `MAX_INLINE_DEPTH`.
    curSeq: long, curLabel: long, topCaller: long, stack: Vec<long>,
    sites: Vec<long>,             // per function, how many calls name it in the whole program
    sizes: Vec<long>,             // per function, the instructions a copy of it brings (-1: none)
    guards: Vec<long>,            // per function, where its leading early-return test ends (`guardEnd`), or -1
    spliceStart: long,            // where the top-level splice being made began in `code`
    nestBudget: long,             // how large that splice may grow by splicing its own calls
    nBodies: long, nSites: long, nTails: long, nSingle: long, nGuardBodies: long, nGuards: long
}

methods Relayout for Default {
    new -> Relayout {
        return Relayout { code: vec![], kinds: vec![], structs: vec![], pointees: vec![],
                          args: vec![], aKinds: vec![], aRegs: vec![], aNames: vec![],
                          aVals: vec![], aText: vec![], aSizes: vec![], tmap: vec![],
                          fnOf: map![], canInline: vec![], orig: vec![], smap: vec![], smapGen: vec![],
                          spliceSeq: 0, lmap: map![], aggName: vec![], aggTemp: vec![], aggSeq: vec![], labelSeq: 0,
                          curSeq: 0, curLabel: 0, topCaller: -1, stack: vec![], sites: vec![], sizes: vec![], guards: vec![], spliceStart: 0, nestBudget: 0,
                          nBodies: 0, nSites: 0, nTails: 0, nSingle: 0, nGuardBodies: 0, nGuards: 0 };
    }
}

methods Relayout {
    run &self inout p:IRProgram -> void {
        self.tmap.clear(); self.smap.clear(); self.smapGen.clear();
        // The new image is at least the old one's size: sized once, rather than grown by doubling
        // (each step a fresh block and a copy of everything so far: the instructions are 136
        // bytes each, and the program's are megabytes).
        self.code.reserve(p.code.len());
        self.args.reserve(p.args.len());
        self.kinds.reserve(p.tempKinds.len());
        self.structs.reserve(p.tempKinds.len());
        self.pointees.reserve(p.tempKinds.len());
        self.tmap.reserve(p.tempKinds.len());
        self.smap.reserve(p.tempKinds.len());
        self.smapGen.reserve(p.tempKinds.len());
        for i in 0..p.tempKinds.len() {
            self.tmap.push(NO_TEMP); self.smap.push(NO_TEMP); self.smapGen.push(-1);
        }
        self.analyze(p);

        for f in 0..p.funcs.len() {
            fn: IRFunc = p.funcs.get(f);
            // Another package's body, here only to be copied: copied, it is done with.
            if (fn.imported) { continue; }
            firstInstr: long = self.code.len();
            firstTemp: Temp = self.kinds.len();
            // A call to itself in return position becomes a jump back to just past the parameter
            // seeds, with the arguments as the parameters' new values.
            tails: bool = self.tailCallable(p, fn);
            top: Sym = NO_SYM;
            if (tails) { top = internString(format(".TC{}", f)); }
            seeding: bool = true;
            for k in 0..fn.instrCount {
                in: Instr = p.code.get(fn.firstInstr + k);
                if (seeding && in.op != IROp.Nop && !(in.op == IROp.Load && in.paramSeed)) {
                    seeding = false;
                    if (tails) { lb: Instr = instr(IROp.Label); lb.name = top; self.code.push(lb); }
                }
                if (tails && self.isTailCall(p, fn, k)) { self.loopBack(p, fn, in, top); continue; }
                self.topCaller = f;
                at: long = self.inlineTarget(p, f, in);
                // A body taken for its one call site only while the caller stays within bounds.
                if (at >= 0 && self.sizes.get(at) > MAX_INLINE_INSTRS
                    && (self.code.len() - firstInstr) + (fn.instrCount - k) + self.sizes.get(at) > MAX_SINGLE_CALLER) { at = -1; }
                if (at >= 0) {
                    // A body copied to its one call site has its own calls spliced in turn, up to the
                    // size such a body may have: nothing it brings is duplicated. One copied to every
                    // call site keeps its calls (each splice of it would carry every copy it made:
                    // measured on this compiler, 18% more code and twice the time in `flow.k`, for
                    // nothing the benchmarks could see).
                    self.spliceStart = self.code.len();
                    self.nestBudget = 0;
                    if (self.sites.get(at) == 1) { self.nestBudget = MAX_SINGLE_INSTRS; }
                    self.splice(p, at, in, 0);
                }
                else if (self.guardTarget(p, in) >= 0) { self.spliceGuard(p, self.guardTarget(p, in), in, 0); }
                else { self.copyInstr(p, in); }
            }
            // The promotion reservations, so nothing is left holding an id from the old
            // numbering. One the optimizer declined is renumbered too and stays unused, which
            // costs an entry in the tables and nothing else.
            for k in 0..fn.promoCount {
                a2: long = fn.firstPromo + k;
                p.promoTemp.set(a2, self.mapTemp(p, p.promoTemp.get(a2)));
            }
            // An `IRFunc` is all scalars, so the copy is edited and put back rather than every
            // field being written out a second time.
            fn.firstInstr = firstInstr;
            fn.instrCount = self.code.len() - firstInstr;
            fn.firstTemp = firstTemp;
            fn.tempCount = self.kinds.len();
            p.funcs.set(f, fn);
        }

        p.code = take(&self.code);
        p.tempKinds = take(&self.kinds);
        p.tempStructs = take(&self.structs);
        p.tempPointees = take(&self.pointees);
        p.args = take(&self.args);
        p.asmKinds = take(&self.aKinds);
        p.asmRegs = take(&self.aRegs);
        p.asmNames = take(&self.aNames);
        p.asmVals = take(&self.aVals);
        p.asmText = take(&self.aText);
        p.asmSizes = take(&self.aSizes);
        // The imported bodies are always the last functions (`importInlinable` appends them).
        while (p.funcs.len() > 0 && p.funcs.last().imported) { p.funcs.pop(); }
        if (gTraceOpt) {
            eprintln("inline: {} bodies eligible ({} for their one call site), copied into {} call sites; {} self tail calls made jumps; {} early-return tests copied to {} call sites",
                     self.nBodies, self.nSingle, self.nSites, self.nTails, self.nGuardBodies, self.nGuards);
        }
    }

    // ─── self tail calls ─────────────────────────────────────────────────────

    // Whether a self call in return position may become a jump. Every parameter must be a plain
    // scalar in a register (a promoted seed): an aggregate is copied into this frame by the
    // prologue, and a pointer parameter may name a local of the frame the jump reuses. Nothing may
    // take a local's address or use a hidden scratch slot or `asm`, for the same reason: what one
    // recursion level made in its frame would be the next level's, still live, after the jump.
    tailCallable &self inout p:IRProgram fn:IRFunc -> bool {
        any: bool = false;
        for k in 0..fn.instrCount {
            in: Instr = p.code.get(fn.firstInstr + k);
            if (in.op == IROp.Load && in.paramSeed) {
                if (!in.promoted || in.dst == NO_TEMP || isAggregate(in.kind) || in.kind == Lit.Ptr
                    || in.kind == Lit.Ref || in.kind == Lit.Fn || in.name == sretSym()) { return false; }
                continue;
            }
            if (in.op == IROp.AddrOf || in.op == IROp.AggSlot || in.op == IROp.Asm
                || in.op == IROp.ArrLoad || in.op == IROp.ArrStore) { return false; }
            if (self.isTailCall(p, fn, k)) { any = true; }
        }
        return any;
    }

    // `t = call <this function>(...)` immediately followed by `ret t` (or a void one by `retvoid`).
    isTailCall &self inout p:IRProgram fn:IRFunc k:long -> bool {
        in: Instr = p.code.get(fn.firstInstr + k);
        if (in.op != IROp.Call || in.name != fn.name || in.noReturn) { return false; }
        if (self.seedCount(p, fn) != in.argCount) { return false; }
        j: long = k + 1;
        while (j < fn.instrCount && p.code.get(fn.firstInstr + j).op == IROp.Nop) { j = j + 1; }
        if (j >= fn.instrCount) { return false; }
        r: Instr = p.code.get(fn.firstInstr + j);
        if (r.op == IROp.Ret) { return in.dst != NO_TEMP && r.a == in.dst; }
        return r.op == IROp.RetVoid && in.dst == NO_TEMP;
    }

    // The arguments into fresh temps first, then into the parameters: an argument may itself be
    // a parameter another one is about to overwrite. Then the jump. The `ret` after the call is
    // left to be copied, and is unreachable.
    loopBack &self inout p:IRProgram fn:IRFunc call:Instr top:Sym -> void {
        fresh: Vec<Temp>;
        for k in 0..call.argCount {
            a: Temp = self.mapTemp(p, p.args.get(call.firstArg + k));
            t: Temp = self.kinds.len();
            self.kinds.push(self.kinds.get(a));
            self.structs.push(self.structs.get(a));
            self.pointees.push(self.pointees.get(a));
            mv: Instr = instr(IROp.Mov);
            mv.dst = t; mv.a = a; mv.kind = self.kinds.get(a);
            self.code.push(mv);
            fresh.push(t);
        }
        seen: long = 0;
        for k in 0..fn.instrCount {
            in: Instr = p.code.get(fn.firstInstr + k);
            if (in.op == IROp.Nop) { continue; }
            if (!(in.op == IROp.Load && in.paramSeed)) { break; }
            mv: Instr = instr(IROp.Mov);
            mv.dst = self.mapTemp(p, in.dst);
            mv.a = fresh.get(seen);
            mv.kind = in.kind;
            mv.structName = in.structName;
            self.code.push(mv);
            seen = seen + 1;
        }
        self.pushJump(top);
        self.nTails = self.nTails + 1;
    }

    // ─── which bodies may be copied ──────────────────────────────────────────

    analyze &self inout p:IRProgram -> void {
        self.fnOf.clear();
        self.canInline.clear();
        self.orig.clear();
        self.sites.clear();
        self.sizes.clear();
        self.guards.clear();
        for f in 0..p.funcs.len() {
            self.fnOf.put(nameOf(p.funcs.get(f).name), f);
            self.orig.push(p.funcs.get(f));
            self.sites.push(0);
        }
        // Every call naming a function, and every place its address is taken (a copy of the body
        // would then sit beside the body itself).
        for f in 0..p.funcs.len() {
            fn: IRFunc = p.funcs.get(f);
            for i in 0..fn.instrCount {
                in: Instr = p.code.get(fn.firstInstr + i);
                if ((in.op != IROp.Call && in.op != IROp.FnAddr) || in.name == NO_SYM) { continue; }
                hit: Option<long> = self.fnOf.find(nameOf(in.name));
                match hit { Some(g) { self.sites.set(g, self.sites.get(g) + 1); } None { } }
            }
        }
        for f in 0..p.funcs.len() {
            fn: IRFunc = p.funcs.get(f);
            size: long = copyableSize(p, fn, true);
            ok: bool = size >= 0 && size <= MAX_INLINE_INSTRS;
            // A body called from one place only is copied there however large (up to a bound that
            // keeps one caller from growing past what the later passes handle well): the call goes
            // and nothing is duplicated, since the body itself is then never emitted.
            if (!ok && size >= 0 && size <= MAX_SINGLE_INSTRS && self.sites.get(f) == 1 && !fn.imported
                && !self.emittedAnyway(fn)) {
                ok = true;
                self.nSingle = self.nSingle + 1;
            }
            self.canInline.push(ok);
            self.sizes.push(size);
            ge: long = -1;
            if (!ok) { ge = guardEnd(p, fn); }
            self.guards.push(ge);
            if (ge >= 0) { self.nGuardBodies = self.nGuardBodies + 1; }
            if (ok) { self.nBodies = self.nBodies + 1; }
        }
    }
}

// Whether a body can be copied into a caller of another package (`irpack`): small, and touching
// no frame slot, so the copy needs nothing renamed.
pub inlinableIR inout p:IRProgram fn:IRFunc -> bool {
    size: long = copyableSize(p, fn, false);
    return size >= 0 && size <= MAX_INLINE_INSTRS;
}

// How many instructions a body copied into a caller brings, or -1 when it cannot be copied:
//
//   * an `asm` block names registers and slots the caller knows nothing about;
//   * a parameter's slot read or written by name (one whose address is taken) is filled by the
//     prologue, which a splice does not have.
//
// A local's named slot (an aggregate, an array, a scalar whose address is taken) is renamed per
// splice (`spliceSlot`), so it lands beside the caller's locals, never on one; `slots` false
// refuses those too (a body another package will copy). A hidden scratch slot (`AggSlot`) is
// numbered program-wide, so the callee's lands in the caller's frame as one more slot. Two splices
// of one callee into one caller share it, which is safe because what a callee builds there dies
// with the call: it is copied out before the body ends (a frame's address may not be returned),
// and splices never overlap. An aggregate result (`$sret`) is a parameter like any other: the
// caller's argument 0 is where to write it, and the splice writes there.
local copyableSize inout p:IRProgram fn:IRFunc slots:bool -> long {
    if (fn.isMain || fn.instrCount == 0) { return -1; }
    if (nameOf(fn.name) == "$globalInit") { return -1; }
    real: long = 0;
    for i in 0..fn.instrCount {
        in: Instr = p.code.get(fn.firstInstr + i);
        if (in.op == IROp.Nop) { continue; }
        real = real + 1;
        if (real > MAX_SINGLE_INSTRS && real > MAX_INLINE_INSTRS) { return -1; }    // too large for either rule
        if (in.op == IROp.Load && in.paramSeed) { continue; }
        if (in.op == IROp.Asm) { return -1; }
        // The address of an aggregate taken by value, only ever read through: the splice reads
        // the caller's value where it lies (`readOnlyAggParam`).
        if (in.op == IROp.AddrOf && !in.isGlobal && readOnlyAggParam(p, fn, i)) { continue; }
        named: bool = in.op == IROp.Load || in.op == IROp.Store || in.op == IROp.AddrOf
                      || in.op == IROp.ArrLoad || in.op == IROp.ArrStore;
        if (!named || in.isGlobal) { continue; }
        if (!slots || in.name == NO_SYM || isParamName(p, fn, in.name)) { return -1; }
    }
    return real;
}

// A body that begins `if (test) { return; }`: after its parameter seeds, at most a few pure
// instructions (loads through and arithmetic on the parameters), then an integer compare-and-branch
// whose fall-through is a bare `retvoid`. The index of that branch, or -1.
local guardEnd inout p:IRProgram fn:IRFunc -> long {
    if (fn.isMain || fn.instrCount == 0 || fn.imported) { return -1; }
    defined: Vec<Temp>;
    pure: long = 0;
    i: long = 0;
    while (i < fn.instrCount) {
        in: Instr = p.code.get(fn.firstInstr + i);
        if (in.op == IROp.Nop) { i = i + 1; continue; }
        if (in.op == IROp.Load && in.paramSeed) {
            if (!in.promoted || in.dst == NO_TEMP) { return -1; }
            defined.push(in.dst);
            i = i + 1;
            continue;
        }
        if (in.op == IROp.Jcc) {
            if (in.kind == Lit.Float || in.kind == Lit.Double || in.a == NO_TEMP) { return -1; }
            if (!tempIn(defined, in.a) || (!in.bIsImm && !tempIn(defined, in.b))) { return -1; }
            k: long = i + 1;
            while (k < fn.instrCount && p.code.get(fn.firstInstr + k).op == IROp.Nop) { k = k + 1; }
            if (k >= fn.instrCount || p.code.get(fn.firstInstr + k).op != IROp.RetVoid) { return -1; }
            return i;
        }
        o: IROp = in.op;
        if (!(o == IROp.PtrLoad || o == IROp.Add || o == IROp.Sub || o == IROp.Mul || o == IROp.Shl
              || o == IROp.Shr || o == IROp.BAnd || o == IROp.BOr || o == IROp.BXor || o == IROp.Const
              || o == IROp.Mov) || in.dst == NO_TEMP) { return -1; }
        if (in.a != NO_TEMP && !tempIn(defined, in.a)) { return -1; }
        if (!in.bIsImm && in.b != NO_TEMP && !tempIn(defined, in.b)) { return -1; }
        pure = pure + 1;
        if (pure > 8) { return -1; }
        defined.push(in.dst);
        i = i + 1;
    }
    return -1;
}

// Whether `n` names one of `fn`'s parameters (the leading run of seeds).
local isParamName inout p:IRProgram fn:IRFunc n:Sym -> bool {
    for i in 0..fn.instrCount {
        s: Instr = p.code.get(fn.firstInstr + i);
        if (s.op == IROp.Nop) { continue; }
        if (!(s.op == IROp.Load && s.paramSeed)) { return false; }
        if (s.name == n) { return true; }
    }
    return false;
}

// `t = addrof p` at `at`, where `p` is a parameter that arrives by value as an aggregate (the
// caller hands its address and the prologue copies the bytes into the callee's own slot), and
// `t` is used only as the base of loads: nothing writes the copy and nothing keeps its address,
// so reading the caller's bytes in place is the same as reading the copy. A consuming `self`
// (`Result.unwrap`, `Try.output`) is the common one: without this, every such method was a call.
pub readOnlyAggParam inout p:IRProgram fn:IRFunc at:long -> bool {
    in: Instr = p.code.get(fn.firstInstr + at);
    if (in.dst == NO_TEMP || !isAggParam(p, fn, in.name)) { return false; }
    // The address and what is computed from it by a constant offset (a field's address).
    addrs: Vec<Temp>;
    addrs.push(in.dst);
    k: long = 0;
    while (k < addrs.len()) {
        t: Temp = addrs.get(k);
        k = k + 1;
        for i in 0..fn.instrCount {
            u: Instr = p.code.get(fn.firstInstr + i);
            if ((t == in.dst && i == at) || u.op == IROp.Nop) { continue; }
            if (u.dst == t) {
                if (t != in.dst && u.op == IROp.Add && u.bIsImm) { continue; }   // its definition
                return false;
            }
            if (u.op == IROp.PtrLoad && u.a == t) { continue; }
            // Copied out of (`match self` holds the value in a local of its own first): a read.
            if (u.op == IROp.AggCopy && u.b == t && u.a != t) { continue; }
            if (u.op == IROp.Add && u.a == t && u.bIsImm && u.dst != NO_TEMP) {
                if (!tempIn(addrs, u.dst)) { addrs.push(u.dst); }
                continue;
            }
            if (u.a == t || (!u.bIsImm && u.b == t)) { return false; }
            for j in 0..u.argCount { if (p.args.get(u.firstArg + j) == t) { return false; } }
            for j in 0..u.pieceCount { if (p.asmVals.get(u.firstPiece + j) == t) { return false; } }
        }
    }
    return true;
}
local tempIn ts:Vec<Temp> t:Temp -> bool {
    for x in ts { if (x == t) { return true; } }
    return false;
}
// Whether `n` names a parameter of `fn` that arrives as an aggregate by value (its seed load is
// of an aggregate kind: a struct, a tuple, a sum type).
pub isAggParam inout p:IRProgram fn:IRFunc n:Sym -> bool {
    if (n == NO_SYM) { return false; }
    for i in 0..fn.instrCount {
        s: Instr = p.code.get(fn.firstInstr + i);
        if (s.op == IROp.Nop) { continue; }
        if (!(s.op == IROp.Load && s.paramSeed)) { return false; }
        if (s.name == n) { return isAggregate(s.kind) && !namedScalar(s.kind, s.structName) && s.kind != Lit.Ref; }
    }
    return false;
}

methods Relayout {
    // The function index a call should be replaced by, or -1. Never itself: that is the one shape
    // that would grow without end.
    inlineTarget &self inout p:IRProgram caller:long in:Instr -> long {
        if (in.op != IROp.Call || in.name == NO_SYM) { return -1; }
        hit: Option<long> = self.fnOf.find(nameOf(in.name));
        at: long = -1;
        match hit { Some(x) { at = x; } None { return -1; } }
        if (at == caller) { return -1; }
        if (!self.canInline.get(at)) { return -1; }
        if (self.seedCount(p, self.orig.get(at)) != in.argCount) { return -1; }
        return at;
    }

    // The leading run of parameter seeds, which is how many arguments the body expects. A body
    // whose seeds are not its leading run is not one this pass understands, and is left alone.
    seedCount &self inout p:IRProgram fn:IRFunc -> long {
        n: long = 0;
        i: long = 0;
        while (i < fn.instrCount) {
            in: Instr = p.code.get(fn.firstInstr + i);
            i = i + 1;
            if (in.op == IROp.Nop) { continue; }
            if (in.op == IROp.Load && in.paramSeed) { n = n + 1; continue; }
            i = fn.instrCount;
        }
        return n;
    }

    // A body that is emitted whether or not anything here calls it: in a library, a `pub`
    // function; in a package, every function of its own source, and a generic instance it
    // exports for its dependents to link to. Copying its one call site would leave the body
    // beside the copy, and an instance inlined away is one a dependent compiles again.
    emittedAnyway &self fn:IRFunc -> bool {
        if (!gInlineLibrary && !gKlibMode) { return false; }
        return fn.isPub || (gKlibMode && gInstanceFp.has(nameOf(fn.name)));
    }

    // ─── a callee's early return, tested in the caller ───────────────────────

    // The function a call goes to when only its leading test is to be copied, or -1.
    guardTarget &self inout p:IRProgram in:Instr -> long {
        if (in.op != IROp.Call || in.name == NO_SYM || in.noReturn || in.dst != NO_TEMP) { return -1; }
        hit: Option<long> = self.fnOf.find(nameOf(in.name));
        g: long = -1;
        match hit { Some(x) { g = x; } None { return -1; } }
        if (self.guards.get(g) < 0) { return -1; }
        if (self.seedCount(p, self.orig.get(g)) != in.argCount) { return -1; }
        return g;
    }

    // `f(args)` where f begins `if (test) { return; }`, as `guardEnd` found: the test, copied here
    // over the arguments, and the call only where it would not return at once,
    //
    //     <the test's loads and arithmetic>; jcc .GDn if !test; call f(args); .GDn:
    //
    // The test is pure (loads and arithmetic on the parameters) and runs just where the callee
    // would have run it first thing, so it sees what the callee would; the callee tests again, which
    // changes nothing. What `Vec.push` pays for its growth check is then a compare, not a call.
    spliceGuard &self inout p:IRProgram g:long call:Instr via:long -> void {
        fn: IRFunc = self.orig.get(g);
        self.spliceSeq = self.spliceSeq + 1;
        self.labelSeq = self.labelSeq + 1;
        outer: long = self.curSeq;
        self.curSeq = self.spliceSeq;
        done: Sym = internString(format(".GD{}", self.labelSeq));
        seen: long = 0;
        end: long = self.guards.get(g);
        for i in 0..end + 1 {
            in: Instr = p.code.get(fn.firstInstr + i);
            if (in.op == IROp.Nop) { continue; }
            if (in.op == IROp.Load && in.paramSeed) {
                self.smap.set(in.dst, self.callerTemp(p, p.args.get(call.firstArg + seen), via));
                self.smapGen.set(in.dst, self.curSeq);
                seen = seen + 1;
                continue;
            }
            if (in.op == IROp.Jcc) {
                j: Instr = in;
                j.a = self.spliceTemp(p, in.a);
                if (!in.bIsImm) { j.b = self.spliceTemp(p, in.b); }
                j.cmpOp = negateCompare(in.cmpOp);
                j.name = done;
                self.code.push(j);
                continue;
            }
            out: Instr = in;
            out.dst = self.spliceTemp(p, in.dst);
            out.a = self.spliceTemp(p, in.a);
            if (!in.bIsImm) { out.b = self.spliceTemp(p, in.b); }
            self.code.push(out);
        }
        self.curSeq = outer;
        // The call itself, as the caller's own instruction: the function being copied (`via` 0),
        // or the splice it sits in (whose stamp `curSeq` is again).
        if (via == 0) { self.copyInstr(p, call); } else { self.spliceInstr(p, call); }
        lb: Instr = instr(IROp.Label);
        lb.name = done;
        self.code.push(lb);
        self.nGuards = self.nGuards + 1;
    }

    // ─── copying one body into its caller ────────────────────────────────────

    // The callee's instructions, with its temps freshened, its labels renamed, its parameters
    // bound to the arguments the caller already computed, and each `ret` turned into an
    // assignment and a jump to an end label written after the body.
    splice &self inout p:IRProgram at:long call:Instr via:long -> void {
        fn: IRFunc = self.orig.get(at);
        // The caller's temps: the function being copied (`via` 0), or the splice this call sits
        // in, whose stamp is `via`. Read before this splice takes a stamp of its own.
        dst: Temp = self.callerTemp(p, call.dst, via);
        outerSeq: long = self.curSeq;
        outerLabel: long = self.curLabel;
        aggBase: long = self.aggName.len();
        self.spliceSeq = self.spliceSeq + 1;
        self.labelSeq = self.labelSeq + 1;
        self.curSeq = self.spliceSeq;
        self.curLabel = self.labelSeq;
        self.lmap.clear();
        self.stack.push(at);
        self.nSites = self.nSites + 1;
        endL: Sym = internString(format(".IE{}", self.curLabel));

        seen: long = 0;
        i: long = 0;
        while (i < fn.instrCount) {
            in: Instr = p.code.get(fn.firstInstr + i);
            i = i + 1;
            if (in.op == IROp.Nop) { continue; }
            // A parameter arrives as a value here rather than in a register, so its seed becomes
            // a copy out of the argument. The caller's argument temps are its own, and go through
            // the caller's map.
            if (in.op == IROp.Load && in.paramSeed) {
                argT: Temp = self.callerTemp(p, p.args.get(call.firstArg + seen), via);
                seen = seen + 1;
                // An aggregate by value: what the body reads through its address is the
                // caller's value, where it lies (`readOnlyAggParam` admitted the body).
                if (isAggregate(in.kind) && !namedScalar(in.kind, in.structName) && in.kind != Lit.Ref) {
                    self.aggName.push(in.name);
                    self.aggTemp.push(argT);
                    self.aggSeq.push(self.curSeq);
                }
                // A parameter the body never writes is the argument: point the two at one temp
                // and emit nothing. A parameter is an ordinary local and may be assigned, and
                // then it needs storage of its own or the assignment would land on the caller's
                // value, so the copy is emitted only when the body actually writes it.
                if (!self.writesAgain(p, fn, in.dst, i - 1)) {
                    self.smap.set(in.dst, argT);
                    self.smapGen.set(in.dst, self.curSeq);
                    continue;
                }
                mv: Instr = instr(IROp.Mov);
                mv.dst = self.spliceTemp(p, in.dst);
                mv.a = argT;
                mv.kind = in.kind;
                mv.structName = in.structName;
                self.code.push(mv);
                continue;
            }
            if (in.op == IROp.Ret) {
                if (dst != NO_TEMP) {
                    mv: Instr = instr(IROp.Mov);
                    mv.dst = dst;
                    mv.a = self.spliceTemp(p, in.a);
                    mv.kind = in.kind;
                    mv.structName = in.structName;
                    self.code.push(mv);
                }
                self.pushJump(endL);
                continue;
            }
            if (in.op == IROp.RetVoid) { self.pushJump(endL); continue; }
            if (in.op == IROp.AddrOf && !in.isGlobal && in.name != NO_SYM) {
                arg: Temp = self.aggArgOf(in.name, aggBase);
                if (arg != NO_TEMP) {
                    self.smap.set(in.dst, arg);
                    self.smapGen.set(in.dst, self.curSeq);
                    continue;
                }
            }
            // A local's slot, renamed for this splice: the caller's own locals, and every other
            // splice's, are other places.
            if ((in.op == IROp.Load || in.op == IROp.Store || in.op == IROp.AddrOf
                 || in.op == IROp.ArrLoad || in.op == IROp.ArrStore) && !in.isGlobal && in.name != NO_SYM) {
                in.name = self.spliceSlot(p, in.name);
            }
            // A call in the copied body is copied in turn, where the original caller's would be.
            if (in.op == IROp.Call && self.stack.len() < MAX_INLINE_DEPTH) {
                inner: long = self.nestedTarget(p, in);
                // Within the budget of the top-level splice it sits in.
                if (inner >= 0 && (self.code.len() - self.spliceStart) + self.sizes.get(inner) > self.nestBudget) { inner = -1; }
                if (inner >= 0) {
                    self.splice(p, inner, in, self.curSeq);
                    continue;
                }
            }
            // A call whose callee starts with an early return: that test, copied here.
            if (in.op == IROp.Call && self.guardTarget(p, in) >= 0) {
                self.spliceGuard(p, self.guardTarget(p, in), in, self.curSeq);
                continue;
            }
            self.spliceInstr(p, in);
        }
        end: Instr = instr(IROp.Label);
        end.name = endL;
        self.code.push(end);
        self.stack.pop();
        self.aggName.truncate(aggBase);
        self.aggTemp.truncate(aggBase);
        self.aggSeq.truncate(aggBase);
        self.curSeq = outerSeq;
        self.curLabel = outerLabel;
        self.lmap.clear();
    }

    // A temp of the caller of a splice: the function being copied (`via` 0) through the ordinary
    // map, or an enclosing splice's, through the stamp that splice was given.
    callerTemp &self inout p:IRProgram t:Temp via:long -> Temp {
        if (via == 0) { return self.mapTemp(p, t); }
        return self.spliceTempAt(p, t, via);
    }

    // The caller's address for a by-value aggregate parameter of the splice being copied.
    aggArgOf &self n:Sym from:long -> Temp {
        k: long = self.aggName.len();
        while (k > from) {
            k = k - 1;
            if (self.aggSeq.get(k) == self.curSeq && self.aggName.get(k) == n) { return self.aggTemp.get(k); }
        }
        return NO_TEMP;
    }

    // A named slot of the body being copied, under a name of this splice's own, as wide as the
    // original's.
    spliceSlot &self inout p:IRProgram n:Sym -> Sym {
        made: Sym = internString(format("{}$i{}", nameOf(n), self.curLabel));
        p.noteSlot(made, p.slotBytesOf(n));
        return made;
    }

    // Where a call inside a body being copied should be spliced from, or -1: as `inlineTarget`
    // says, and never a function already being copied (that would grow without end).
    nestedTarget &self inout p:IRProgram in:Instr -> long {
        at: long = self.inlineTarget(p, self.topCaller, in);
        if (at < 0) { return -1; }
        for s in self.stack { if (s == at) { return -1; } }
        return at;
    }

    // Whether the body writes `t` anywhere but at `seedAt`, the instruction that introduced it.
    writesAgain &self inout p:IRProgram fn:IRFunc t:Temp seedAt:long -> bool {
        for i in 0..fn.instrCount {
            in: Instr = p.code.get(fn.firstInstr + i);
            if (i != seedAt && in.dst == t) { return true; }
        }
        return false;
    }

    pushJump &self to:Sym -> void {
        j: Instr = instr(IROp.Jmp);
        j.name = to;
        self.code.push(j);
    }

    // One instruction of a spliced body: the same copy `copyInstr` makes, over the splice's temp
    // map, and with any label it names renamed. The callee's `.L0` and the caller's are two
    // different places, and so are two copies of the same callee.
    spliceInstr &self inout p:IRProgram in:Instr -> void {
        out: Instr = in;
        out.dst = self.spliceTemp(p, in.dst);
        out.a = self.spliceTemp(p, in.a);
        if (!in.bIsImm) { out.b = self.spliceTemp(p, in.b); }
        if (in.op == IROp.Label || isBranch(in.op)) { out.name = self.spliceLabel(in.name); }
        if (in.argCount > 0) {
            out.firstArg = self.args.len();
            for k in 0..in.argCount {
                self.args.push(self.spliceTemp(p, p.args.get(in.firstArg + k)));
            }
        }
        self.code.push(out);
    }

    spliceLabel &self n:Sym -> Sym {
        if (n == NO_SYM) { return n; }
        hit: Option<Sym> = self.lmap.find(nameOf(n));
        match hit { Some(m) { return m; } None { } }
        made: Sym = internString(format(".IL{}_{}", self.curLabel, nameOf(n)));
        self.lmap.put(keep(nameOf(n)), made);
        return made;
    }

    // A temp of the body being spliced, fresh at this site. Stamped with the site's sequence
    // number, so the table is never cleared and a stale entry is one comparison away. A splice
    // nested in another leaves the outer one's entries alone: they are another function's temps.
    spliceTemp &self inout p:IRProgram t:Temp -> Temp { return self.spliceTempAt(p, t, self.curSeq); }

    spliceTempAt &self inout p:IRProgram t:Temp seq:long -> Temp {
        if (t == NO_TEMP || t < 0 || t >= self.smap.len()) { return t; }
        if (self.smapGen.get(t) == seq) { return self.smap.get(t); }
        made: Temp = self.kinds.len();
        self.kinds.push(p.tempKinds.get(t));
        self.structs.push(p.tempStructs.get(t));
        self.pointees.push(p.tempPointees.get(t));
        self.smap.set(t, made);
        self.smapGen.set(t, seq);
        return made;
    }

    // ─── the plain copy ──────────────────────────────────────────────────────

    // One instruction into the new image. Its operands are renumbered, and the two runs it names
    // (its call arguments and its `asm` pieces) are copied into fresh runs of their own, since
    // those vectors are being rebuilt underneath it as well.
    copyInstr &self inout p:IRProgram in:Instr -> void {
        out: Instr = in;
        out.dst = self.mapTemp(p, in.dst);
        out.a = self.mapTemp(p, in.a);
        if (!in.bIsImm) { out.b = self.mapTemp(p, in.b); }
        if (in.argCount > 0) {
            out.firstArg = self.args.len();
            for k in 0..in.argCount {
                self.args.push(self.mapTemp(p, p.args.get(in.firstArg + k)));
            }
        }
        // Six parallel tables, copied together: an `asm` piece is one row across all of them, and
        // one of them indexing differently is what the comment on `firstPiece` warns about.
        if (in.pieceCount > 0) {
            out.firstPiece = self.aVals.len();
            for k in 0..in.pieceCount {
                j: long = in.firstPiece + k;
                self.aKinds.push(p.asmKinds.get(j));
                self.aRegs.push(p.asmRegs.get(j));
                self.aNames.push(p.asmNames.get(j));
                self.aVals.push(self.mapTemp(p, p.asmVals.get(j)));
                self.aText.push(p.asmText.get(j));
                self.aSizes.push(p.asmSizes.get(j));
            }
        }
        self.code.push(out);
    }

    // A temp in the new numbering, made on first mention. Its type and its pointee travel with
    // it: `tempPointees` is what makes `p + n` scale and `*p` load the right width, and a
    // renumbering that dropped it would turn every typed pointer into a raw address.
    mapTemp &self inout p:IRProgram t:Temp -> Temp {
        if (t == NO_TEMP || t < 0 || t >= self.tmap.len()) { return t; }
        got: Temp = self.tmap.get(t);
        if (got != NO_TEMP) { return got; }
        made: Temp = self.kinds.len();
        self.kinds.push(p.tempKinds.get(t));
        self.structs.push(p.tempStructs.get(t));
        self.pointees.push(p.tempPointees.get(t));
        self.tmap.set(t, made);
        return made;
    }

    // How many temps the program now has, for a pass that wants to make more of them.
    tempCount &self -> long { return self.kinds.len(); }
}
