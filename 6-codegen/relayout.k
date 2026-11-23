// The inliner. It rebuilds the program so that a function can grow, which is what inlining needs.
//
// The instruction list is one flat vector that each `IRFunc` names a run in, and temps are
// numbered program-wide with every function owning a contiguous range, so no pass can insert an
// instruction in place. This one copies each function into a fresh image, renumbering as it
// goes, and splices callee bodies in on the way: small bodies at every call site, larger ones
// at their only call site, a callee's leading `if (test) { return; }` where the rest of its body
// stays a call, and a self call in return position as a jump back to the top. In a loop, a body
// whose copy would make no call at all is copied with its own calls copied in turn (`callFree`).
#include <{ir, opt}>
#include <parse::{types, upstream}>
#include <support::compiler>
#include <stdlib::{fmt, map, mem, option, string, vec}>

// How big a body may be and still be worth copying into its callers, its parameter seeds not
// counted. `Vec.at` (the bounds check, the element address and the load) is twenty, and it is
// the one that matters.
// `--no-forward-inline`: a body that only hands its call on keeps its callee a call when it is
// copied to many sites (`forwardingBody`).
pub var gForwardInlineOff: bool = false;
// `--no-free-seeds`: a body's parameter seeds count toward its size, as they did. Copied, each is
// a move from the argument that copy propagation removes, so they cost nothing; counted, a
// two-parameter body of 23 instructions (`Vec<T>.push` of a struct) weighed 25 and stayed a call.
pub var gFreeSeedsOff: bool = false;
// `--no-splice-slots`: every copy of a body shares the body's scratch slots (`spliceInstr`).
pub var gSpliceSlotsOff: bool = false;
// `--no-accumulate`: a call whose result its caller only combines with a value and returns
// stays a call (`accOf`).
pub var gAccumulateOff: bool = false;

// The identity of an operator `accOf` accumulates with.
local accIdentity op:IROp -> long {
    if (op == IROp.Mul) { return 1; }
    if (op == IROp.BAnd) { return -1; }
    return 0;
}

local MAX_INLINE_INSTRS: long = 24;

// A body called from exactly one place is copied there up to this size: nothing is duplicated, and
// the bound keeps one caller from growing past what `flow.k` and the allocator handle well.
local MAX_SINGLE_INSTRS: long = 160;

// How deep a spliced body's own calls are spliced in turn.
local MAX_INLINE_DEPTH: long = 4;

// A caller grows by bodies taken for their one call site only up to this size: past it, the
// dataflow in `flow.k` costs more than the calls it saves.
local MAX_SINGLE_CALLER: long = 1000;

// A short loop all of whose calls copies can take away (`closableLoops`): a loop of at most
// `CLOSE_SPAN` instructions, as the lowerer wrote it, in which each copy may bring up to
// `CLOSE_INSTRS`, slow paths aside.
local CLOSE_SPAN: long = 40;
local CLOSE_INSTRS: long = 48;

// A `--lib` build (main.k sets it): every `pub` function is emitted whatever calls it.
pub var gInlineLibrary: bool = false;

// `--no-loop-inline`: no call-free copies in loops (`callFree`, `closableLoops`).
pub var gLoopInlineOff: bool = false;

local CF_UNKNOWN: long = -2;
local NO_SPAN: long = 1 << 40;

// Where `callFree` keeps its answer for body `g` with `levels` of nesting below it.
local cfKey g:long levels:long guarded:bool -> long {
    k: long = (g * MAX_INLINE_DEPTH + levels) * 2;
    if (guarded) { k = k + 1; }
    return k;
}

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
    fnOf: HashMap<long, long>,    // function name (its number) -> its index, for finding a call's target
    canInline: Vec<bool>,         // per function, decided once by `inlinableBody`
    // Every function's runs as they were. `p.funcs` is rewritten in place as each one is copied,
    // so by the time a later caller wants a callee's body, the entry for it already names the
    // new image while the body still has to be read out of the old one.
    orig: Vec<IRFunc>,
    // A spliced body's temps are fresh at every site, so they cannot share `tmap`, which is keyed
    // by the old id for the whole program. Stamped rather than cleared: clearing a table the size
    // of the program once per call site is exactly the cost this pass exists to avoid.
    smap: Vec<Temp>, smapGen: Vec<long>, spliceSeq: long,
    lmap: HashMap<long, Sym>,     // a spliced body's labels (by number), renamed per site
    amap: HashMap<long, long>,    // a spliced body's scratch slots (`AggSlot`), one per site: by stamp and slot
    // A spliced body's by-value aggregate parameters: the caller's address, per splice (`aggSeq`).
    aggName: Vec<Sym>, aggTemp: Vec<Temp>, aggSeq: Vec<long>,
    labelSeq: long,
    // The splice being copied (its stamp and its label number), and the functions whose bodies
    // are being copied, outermost first: a call inside a spliced body is spliced in turn, never
    // into itself and never past `MAX_INLINE_DEPTH`.
    curSeq: long, curLabel: long, topCaller: long, stack: Vec<long>,
    sites: Vec<long>,             // per function, how many calls name it in the whole program
    sizes: Vec<long>,             // per function, the instructions a copy of it brings (-1: none)
    forwards: Vec<bool>,          // per function, whether its body only hands its call on (`forwardingBody`)
    guards: Vec<long>,            // per function, where its leading early-return test ends (`guardEnd`), or -1
    spliceStart: long,            // where the top-level splice being made began in `code`
    nestBudget: long,             // how large that splice may grow by splicing its own calls
    seeds: Vec<long>,             // per function, its parameter seeds (`seedCount`)
    loopy: Vec<long>,             // per function, whether its body has a loop: 1, 0, or -1 not asked yet
    // ─── call-free copies in loops ──────────────────────────────────────────
    // Per body, levels of nesting below it and whether slow paths are set aside, the size of a
    // copy that makes no call (`callFree`), -1 for none, CF_UNKNOWN before it is asked; and
    // whether that copy has a loop.
    cfMemo: Vec<long>, cfLoop: Vec<bool>,
    // A label's place in the body being walked for its loops, stamped so the table is never
    // cleared (`loopDepths`); the short loops that walk found (`closableLoops`).
    labelAt: HashMap<long, long>, labelStamp: long,
    shortH: Vec<long>, shortJ: Vec<long>,
    curDepth: long,               // how many loops hold the call whose body is being copied
    forceNest: bool,              // the splice being made is a call-free copy: every call in it is copied
    forceGuard: bool,             // ...but a callee's leading early return, where set aside (`spliceGuard`)
    nBodies: long, nSites: long, nTails: long, nSingle: long, nGuardBodies: long, nGuards: long,
    nCallFree: long, nClosed: long,
    // The function being walked accumulates its own calls' results (`accOf`): the operands' kind;
    // and, for the site `accSite` last answered, its operator's index, its other operand, and
    // whether that operand is an immediate.
    accKind: Lit, accAt: long, accOther: Temp, accImm: bool, nAccs: long
}

methods Relayout for Default {
    new -> Relayout {
        return Relayout { code: vec![], kinds: vec![], structs: vec![], pointees: vec![],
                          args: vec![], aKinds: vec![], aRegs: vec![], aNames: vec![],
                          aVals: vec![], aText: vec![], aSizes: vec![], tmap: vec![],
                          fnOf: map![], canInline: vec![], orig: vec![], smap: vec![], smapGen: vec![],
                          spliceSeq: 0, lmap: map![], amap: map![], aggName: vec![], aggTemp: vec![], aggSeq: vec![], labelSeq: 0,
                          curSeq: 0, curLabel: 0, topCaller: -1, stack: vec![], sites: vec![], sizes: vec![], forwards: vec![], guards: vec![], spliceStart: 0, nestBudget: 0,
                          seeds: vec![], loopy: vec![], cfMemo: vec![], cfLoop: vec![], labelAt: map![], labelStamp: 0,
                          shortH: vec![], shortJ: vec![], curDepth: 0, forceNest: false, forceGuard: false,
                          nBodies: 0, nSites: 0, nTails: 0, nSingle: 0, nGuardBodies: 0, nGuards: 0, nCallFree: 0, nClosed: 0,
                          accKind: Lit.Long, accAt: -1, accOther: NO_TEMP, accImm: false, nAccs: 0 };
    }
}

methods Relayout {
    run &self inout p:IRProgram -> void {
        p.slotFn = NO_SYM;      // what the lowerer was in: a splice notes its slots for its caller
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

        depths: Vec<long>;
        closable: Vec<bool>;
        for f in 0..p.funcs.len() {
            fn: IRFunc = p.funcs.get(f);
            // Another package's body, here only to be copied: copied, it is done with.
            if (fn.imported) { continue; }
            firstInstr: long = self.code.len();
            firstTemp: Temp = self.kinds.len();
            // A call to itself in return position becomes a jump back to just past the parameter
            // seeds, with the arguments as the parameters' new values.
            tails: bool = self.tailCallable(p, fn);
            // `return x + f(...)`: the call's result accumulated, the call a jump (`accOf`).
            accOp: IROp = self.accOf(p, fn);
            acc: Temp = NO_TEMP;
            if (accOp != IROp.Nop) { tails = true; }
            top: Sym = NO_SYM;
            if (tails) { top = madeName(".TC", f, ""); }
            seeding: bool = true;
            self.loopDepths(p, fn, &depths);
            self.closableLoops(p, f, fn, &closable);
            // Where the function begins with a test that returns a parameter or a constant
            // (`fib`'s `n < 2`, `leadReturn`), the loop is turned so that test comes at its
            // bottom: it is written once ahead of the loop, its return there giving the value
            // alone, and again in place of each jump back, its return there combining it with
            // what was accumulated:
            //
            //     if (n >= 2) goto P; return n;
            //     P: acc = 0;
            //     L: ... acc = acc + t; n = n - 2; if (n >= 2) goto L; return acc + n;
            //
            // A call that returns at once still makes no frame (the emitter's `emitGuard` moves
            // that first test above the prologue), and a turn makes one test and no jump.
            // Otherwise the accumulator is set before the loop's top.
            leadK: long = -1;
            leadG: long = -1;
            leadL: Sym = NO_SYM;
            pendAt: long = -1;
            pendCall: Instr = instr(IROp.Nop);
            pendOther: Temp = NO_TEMP;
            pendImm: bool = false;
            for k in 0..fn.instrCount {
                in: Instr = p.code.get(fn.firstInstr + k);
                if (seeding && in.op != IROp.Nop && !(in.op == IROp.Load && in.paramSeed)) {
                    seeding = false;
                    if (accOp != IROp.Nop) {
                        acc = self.kinds.len();
                        self.kinds.push(self.accKind);
                        self.structs.push(NO_SYM);
                        self.pointees.push(NO_SYM);
                        leadG = self.leadReturn(p, fn, k);
                        if (leadG >= 0) {
                            leadK = k;
                            leadL = p.code[fn.firstInstr + k].name;
                            pre: Sym = madeName(".AP", f, "");
                            self.leadCopy(p, fn, leadK, leadG, pre, accOp, NO_TEMP);
                            lp: Instr = instr(IROp.Label);
                            lp.name = pre;
                            self.code.push(lp);
                        }
                        self.code.push(self.accInit(acc, accOp));
                    }
                    if (tails && leadG < 0) { lb: Instr = instr(IROp.Label); lb.name = top; self.code.push(lb); }
                }
                // The test itself, written ahead of the loop and at its bottom instead.
                if (leadG >= 0 && k >= leadK && k <= leadG) { continue; }
                // An accumulated call is dropped where it is, what computes the other operand is
                // copied as it comes, and at the operator: `acc = acc op x`, then the call's
                // arguments into the parameters and back.
                if (accOp != IROp.Nop && self.accSite(p, fn, k) != IROp.Nop) {
                    pendAt = self.accAt;
                    pendCall = in;
                    pendOther = self.accOther;
                    pendImm = self.accImm;
                    continue;
                }
                if (k == pendAt) {
                    pendAt = -1;
                    up: Instr = instr(accOp);
                    up.dst = acc;
                    up.a = acc;
                    up.kind = self.accKind;
                    if (pendImm) { up.bIsImm = true; up.bImm = in.bImm; }
                    else { up.b = self.mapTemp(p, pendOther); }
                    self.code.push(up);
                    self.loopMoves(p, fn, pendCall);
                    if (leadG >= 0) { self.leadCopy(p, fn, leadK, leadG, leadL, accOp, acc); }
                    else { self.pushJump(top); }
                    self.nTails = self.nTails + 1;
                    self.nAccs = self.nAccs + 1;
                    continue;
                }
                if (tails && self.isTailCall(p, fn, k)) {
                    self.loopMoves(p, fn, in);
                    if (leadG >= 0) { self.leadCopy(p, fn, leadK, leadG, leadL, accOp, acc); }
                    else { self.pushJump(top); }
                    self.nTails = self.nTails + 1;
                    continue;
                }
                // Every other return gives back what was accumulated combined with its value.
                if (accOp != IROp.Nop && in.op == IROp.Ret) {
                    r: Temp = self.kinds.len();
                    self.kinds.push(self.accKind);
                    self.structs.push(NO_SYM);
                    self.pointees.push(NO_SYM);
                    fin: Instr = instr(accOp);
                    fin.dst = r;
                    fin.a = acc;
                    fin.b = self.mapTemp(p, in.a);
                    fin.kind = self.accKind;
                    self.code.push(fin);
                    rt: Instr = instr(IROp.Ret);
                    rt.a = r;
                    rt.kind = in.kind;
                    self.code.push(rt);
                    continue;
                }
                self.topCaller = f;
                at: long = self.inlineTarget(p, f, in);
                // A call in a `recover` body stays a call: its fault edge says the handler may follow
                // it, which a copy of its body would have to say after each of its own calls.
                faulty: bool = k + 1 < fn.instrCount && p.code[fn.firstInstr + k + 1].op == IROp.FaultEdge;
                if (faulty) { at = -1; }
                // In a short loop whose every call a copy takes away (`closableLoops`), the copy,
                // with its own calls copied in turn but its slow paths left as calls: with no call
                // on its fast path, what the loop holds stays in registers. Elsewhere in a loop, a
                // body copied as any small one has its call-free callees copied with it (`splice`).
                free: long = -1;
                if (!faulty && !gLoopInlineOff && in.op == IROp.Call && !in.noReturn && closable.len() > 0 && closable.get(k)) {
                    g: long = self.calleeAt(in);
                    if (g >= 0 && g != f) {
                        free = self.callFree(p, g, MAX_INLINE_DEPTH - 1, true);
                        if (free > CLOSE_INSTRS || self.cfLoop.get(cfKey(g, MAX_INLINE_DEPTH - 1, true))) { free = -1; }
                        if (free >= 0) { at = g; }
                    }
                }
                if (at >= 0 && self.sites.get(at) > 1 && towardNever(p, fn, k)) { at = -1; }
                // A body taken for its one call site only while the caller stays within bounds.
                grows: long = free;
                if (at >= 0 && free < 0) { grows = self.sizes.get(at); }
                if (at >= 0 && grows > MAX_INLINE_INSTRS
                    && (self.code.len() - firstInstr) + (fn.instrCount - k) + grows > MAX_SINGLE_CALLER) { at = -1; }
                if (at >= 0 && free >= 0) {
                    self.spliceStart = self.code.len();
                    self.nestBudget = 0;
                    self.curDepth = depths.get(k);
                    self.forceNest = true;
                    self.forceGuard = true;
                    self.splice(p, at, in, 0);
                    self.forceNest = false;
                    self.forceGuard = false;
                    self.nClosed = self.nClosed + 1;
                }
                else if (at >= 0) {
                    // A body copied to its one call site has its own calls spliced in turn, up
                    // to the size such a body may have, since nothing it brings is duplicated. A
                    // body copied to every call site keeps its calls: each splice of it would
                    // carry every copy it made, which on this compiler measured 18% more code
                    // and twice the time in `flow.k`, for nothing the benchmarks could see.
                    self.spliceStart = self.code.len();
                    self.nestBudget = 0;
                    if (self.sites.get(at) == 1) { self.nestBudget = MAX_SINGLE_INSTRS; }
                    self.curDepth = depths.get(k);
                    self.splice(p, at, in, 0);
                }
                else if (!faulty && self.guardTarget(p, in) >= 0) { self.spliceGuard(p, self.guardTarget(p, in), in, 0); }
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
            eprintln("inline: {} bodies eligible ({} for their one call site), copied into {} call sites; {} self tail calls made jumps; {} early-return tests copied to {} call sites; {} call-free copies in loops; {} copies closing a loop",
                     self.nBodies, self.nSingle, self.nSites, self.nTails, self.nGuardBodies, self.nGuards, self.nCallFree, self.nClosed);
        }
    }

    // ─── self tail calls ─────────────────────────────────────────────────────

    // Whether a self call in return position may become a jump. Every parameter must be a plain
    // scalar in a register (a promoted seed): an aggregate is copied into this frame by the
    // prologue, and a pointer parameter may name a local of the frame the jump reuses. Nothing may
    // take a local's address or use a hidden scratch slot or `asm`, for the same reason: what one
    // recursion level made in its frame would be the next level's, still live, after the jump.
    tailCallable &self inout p:IRProgram fn:IRFunc -> bool {
        if (!self.tailShape(p, fn)) { return false; }
        for k in 0..fn.instrCount {
            if (self.isTailCall(p, fn, k)) { return true; }
        }
        return false;
    }

    // Whether a jump back to the top may stand for a call to itself, by the rules above.
    tailShape &self inout p:IRProgram fn:IRFunc -> bool {
        for k in 0..fn.instrCount {
            in: Instr = p.code.get(fn.firstInstr + k);
            if (in.op == IROp.Load && in.paramSeed) {
                if (!in.promoted || in.dst == NO_TEMP || isAggregate(in.kind) || in.kind == Lit.Ptr
                    || in.kind == Lit.Ref || in.kind == Lit.Fn || in.name == sretSym()) { return false; }
                continue;
            }
            if (in.op == IROp.AddrOf || in.op == IROp.AggSlot || in.op == IROp.Asm
                || in.op == IROp.ArrLoad || in.op == IROp.ArrStore) { return false; }
        }
        return true;
    }

    // `t = call <this function>(...)` immediately followed by `ret t` (or a void one by `retvoid`).
    isTailCall &self inout p:IRProgram fn:IRFunc k:long -> bool {
        in: Instr = p.code.get(fn.firstInstr + k);
        if (in.op != IROp.Call || in.name != fn.name || in.noReturn) { return false; }
        if (self.seedCount(p, fn) != in.argCount) { return false; }
        j: long = k + 1;
        while (j < fn.instrCount && p.code[fn.firstInstr + j].op == IROp.Nop) { j = j + 1; }
        if (j >= fn.instrCount) { return false; }
        r: Instr = p.code.get(fn.firstInstr + j);
        if (r.op == IROp.Ret) { return in.dst != NO_TEMP && r.a == in.dst; }
        return r.op == IROp.RetVoid && in.dst == NO_TEMP;
    }

    // ─── a call whose result is accumulated ──────────────────────────────────

    // The operator a function combines its own calls' results with, when it may run them as a
    // loop; Nop otherwise. Every `return x op f(...)` (or `f(...) op x`) in it uses the same `op`,
    // one of `+ * & | ^` on an integer, which wrapping keeps associative and commutative: so
    // `f(n)` is `acc op` the value the last turn returns, `acc` starting as the operator's
    // identity, and the call becomes `acc = acc op x` and a jump back with its arguments. Every
    // other return gives back `acc op v`, and a plain tail call is a jump that leaves `acc`
    // alone. `fib`'s second call is such a call: the first stays a call, the second a loop. The
    // function has to be one whose self tail calls could be jumps (`tailShape`), every return of
    // a value of that integer kind.
    accOf &self inout p:IRProgram fn:IRFunc -> IROp {
        if (gAccumulateOff || !self.tailShape(p, fn)) { return IROp.Nop; }
        op: IROp = IROp.Nop;
        for k in 0..fn.instrCount {
            in: Instr = p.code.get(fn.firstInstr + k);
            if (in.op == IROp.RetVoid) { return IROp.Nop; }
            if (in.op == IROp.Ret && (in.a == NO_TEMP || !isInteger(in.kind))) { return IROp.Nop; }
            s: IROp = self.accSite(p, fn, k);
            if (s == IROp.Nop) { continue; }
            if (op != IROp.Nop && (s != op || self.accKind != in.kind)) { return IROp.Nop; }
            op = s;
            self.accKind = in.kind;
        }
        return op;
    }

    // At `k`, `t = call <this function>(...)`, then (Nops aside) `u = t op x` or `u = x op t`,
    // `x` not `t`, then `ret u`, all at one integer kind: the operator, with `accAt`, `accOther`
    // and `accImm` saying where it is and what `x` is. Nop for anything else.
    accSite &self inout p:IRProgram fn:IRFunc k:long -> IROp {
        in: Instr = p.code.get(fn.firstInstr + k);
        if (in.op != IROp.Call || in.name != fn.name || in.noReturn || in.dst == NO_TEMP) { return IROp.Nop; }
        if (!isInteger(in.kind) || self.seedCount(p, fn) != in.argCount) { return IROp.Nop; }
        t: Temp = in.dst;
        // Between the call and the operator, arithmetic computing the other operand
        // (`f(n - 1) + n * n` evaluates `n * n` after the call): it may stay where it is, as
        // long as it neither reads the result nor writes what the call was handed.
        j: long = self.nextReal(fn, p, k + 1);
        while (j < fn.instrCount && betweenOk(p.code.get(fn.firstInstr + j), t)) {
            w: Temp = p.code[fn.firstInstr + j].dst;
            for q in 0..in.argCount { if (p.args.get(in.firstArg + q) == w) { return IROp.Nop; } }
            j = self.nextReal(fn, p, j + 1);
        }
        if (j >= fn.instrCount) { return IROp.Nop; }
        u: Instr = p.code.get(fn.firstInstr + j);
        if (u.op != IROp.Add && u.op != IROp.Mul && u.op != IROp.BAnd && u.op != IROp.BOr && u.op != IROp.BXor) { return IROp.Nop; }
        if (u.kind != in.kind || u.dst == NO_TEMP) { return IROp.Nop; }
        if (u.bIsImm) {
            if (u.a != t) { return IROp.Nop; }
            self.accImm = true;
            self.accOther = NO_TEMP;
        } else if (u.a == t && u.b != t) {
            self.accImm = false;
            self.accOther = u.b;
        } else if (u.b == t && u.a != t) {
            self.accImm = false;
            self.accOther = u.a;
        } else { return IROp.Nop; }
        r: long = self.nextReal(fn, p, j + 1);
        if (r >= fn.instrCount) { return IROp.Nop; }
        rt: Instr = p.code.get(fn.firstInstr + r);
        if (rt.op != IROp.Ret || rt.a != u.dst || rt.kind != in.kind) { return IROp.Nop; }
        self.accAt = j;
        return u.op;
    }

    // `acc = <the operator's identity>`.
    accInit &self acc:Temp op:IROp -> Instr {
        c0: Instr = instr(IROp.Const);
        c0.dst = acc;
        c0.imm = accIdentity(op);
        c0.kind = self.accKind;
        return c0;
    }

    // At `k`, the first instruction past the seeds: an integer compare and branch on parameters
    // whose fall-through only returns a parameter or a constant (constants made, then `ret`), and
    // whose target is the label right after that `ret`. The index of the `ret`, or -1.
    leadReturn &self inout p:IRProgram fn:IRFunc k:long -> long {
        jc: Instr = p.code.get(fn.firstInstr + k);
        if (jc.op != IROp.Jcc || !isInteger(jc.kind)) { return -1; }
        if (!isSeedTemp(p, fn, jc.a) || (!jc.bIsImm && !isSeedTemp(p, fn, jc.b))) { return -1; }
        made: Vec<Temp>;
        g: long = -1;
        j: long = k + 1;
        while (j < fn.instrCount && g < 0) {
            c: Instr = p.code.get(fn.firstInstr + j);
            if (c.op == IROp.Const && c.dst != NO_TEMP) { made.push(c.dst); }
            else if (c.op == IROp.Ret) {
                if (!isSeedTemp(p, fn, c.a) && !tempIn(made, c.a)) { return -1; }
                g = j;
            } else if (c.op != IROp.Nop) { return -1; }
            j = j + 1;
        }
        if (g < 0) { return -1; }
        n: long = self.nextReal(fn, p, g + 1);
        if (n < fn.instrCount && p.code[fn.firstInstr + n].op == IROp.Label && p.code[fn.firstInstr + n].name == jc.name) { return g; }
        return -1;
    }

    // The first instruction of `fn` at or after `k` that is not a Nop (`instrCount` if none).
    nextReal &self fn:IRFunc inout p:IRProgram k:long -> long {
        j: long = k;
        while (j < fn.instrCount && p.code[fn.firstInstr + j].op == IROp.Nop) { j = j + 1; }
        return j;
    }

    // The arguments into fresh temps first, then into the parameters: an argument may itself be
    // a parameter another one is about to overwrite. Then the jump. The `ret` after the call is
    // left to be copied, and is unreachable.
    loopBack &self inout p:IRProgram fn:IRFunc call:Instr top:Sym -> void {
        self.loopMoves(p, fn, call);
        self.pushJump(top);
        self.nTails = self.nTails + 1;
    }

    // The function's leading test and the return it guards (instructions `from` to `to`, from
    // `leadReturn`), copied: the branch to `target`, and the return giving `acc op v` where
    // `acc` is given, `v` alone where it is not.
    leadCopy &self inout p:IRProgram fn:IRFunc from:long to:long target:Sym op:IROp acc:Temp -> void {
        for j in from..to + 1 {
            c: Instr = p.code.get(fn.firstInstr + j);
            if (c.op == IROp.Nop) { continue; }
            if (c.op == IROp.Ret && acc != NO_TEMP) {
                r: Temp = self.kinds.len();
                self.kinds.push(self.accKind);
                self.structs.push(NO_SYM);
                self.pointees.push(NO_SYM);
                fin: Instr = instr(op);
                fin.dst = r;
                fin.a = acc;
                fin.b = self.mapTemp(p, c.a);
                fin.kind = self.accKind;
                self.code.push(fin);
                c.a = r;
                self.code.push(c);
                continue;
            }
            if (c.op == IROp.Jcc) { c.name = target; }
            c.dst = self.mapTemp(p, c.dst);
            c.a = self.mapTemp(p, c.a);
            if (!c.bIsImm) { c.b = self.mapTemp(p, c.b); }
            self.code.push(c);
        }
    }

    // A self call's arguments into the parameters, through fresh temps.
    loopMoves &self inout p:IRProgram fn:IRFunc call:Instr -> void {
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
    }

    // ─── which bodies may be copied ──────────────────────────────────────────

    analyze &self inout p:IRProgram -> void {
        self.fnOf.clear();
        self.canInline.clear();
        self.orig.clear();
        self.sites.clear();
        self.sizes.clear();
        self.guards.clear();
        self.seeds.clear();
        self.loopy.clear();
        self.cfMemo.clear();
        self.cfLoop.clear();
        for f in 0..p.funcs.len() {
            self.fnOf.put((p.funcs.get(f).name) as long, f);
            self.orig.push(p.funcs.get(f));
            self.sites.push(0);
            self.seeds.push(self.seedCount(p, p.funcs.get(f)));
            self.loopy.push(-1);
            for k in 0..MAX_INLINE_DEPTH * 2 { self.cfMemo.push(CF_UNKNOWN); self.cfLoop.push(false); }
        }
        // Every call naming a function, and every place its address is taken (a copy of the body
        // would then sit beside the body itself).
        for f in 0..p.funcs.len() {
            fn: IRFunc = p.funcs.get(f);
            for i in 0..fn.instrCount {
                in: Instr = p.code.get(fn.firstInstr + i);
                if ((in.op != IROp.Call && in.op != IROp.FnAddr) || in.name == NO_SYM) { continue; }
                hit: Option<long> = self.fnOf.find(in.name as long);
                match hit { Some(g) { self.sites.set(g, self.sites.get(g) + 1); } None { } }
            }
        }
        for f in 0..p.funcs.len() {
            fn: IRFunc = p.funcs.get(f);
            size: long = copyableSize(p, fn, true);
            // A small body is copied to every call site, unless it holds a loop: its call costs
            // little against the trips it makes, and every copy would bring the whole loop into
            // a caller whose registers its own values already hold. Measured on this compiler,
            // copying those cost 9% more instructions compiling itself, for nothing the
            // benchmarks could see.
            ok: bool = size >= 0 && size <= MAX_INLINE_INSTRS && !self.loopyOf(p, f);
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
            self.forwards.push(!gForwardInlineOff && ok && forwardingBody(p, fn));
            ge: long = -1;
            if (!ok) { ge = guardEnd(p, fn); }
            self.guards.push(ge);
            if (ge >= 0) { self.nGuardBodies = self.nGuardBodies + 1; }
            if (ok) { self.nBodies = self.nBodies + 1; }
        }
    }
}

// A body that only hands its call on: its one call (to a function that returns), at most
// `FORWARD_OWN` instructions of its own before it (the parameters' seeds aside) and, after it,
// only its result returned (an aggregate's bytes copied to where the body's own goes); no branch.
// `Ast.expr`, `self.exprs.get(id)`, is one.
local FORWARD_OWN: long = 4;
local forwardingBody inout p:IRProgram fn:IRFunc -> bool {
    calls: long = 0;
    own: long = 0;
    res: Temp = NO_TEMP;          // the call's result, and a copy of it
    sret: Temp = NO_TEMP;         // the address an aggregate result is written to
    for i in 0..fn.instrCount {
        ix: long = fn.firstInstr + i;
        o: IROp = p.code[ix].op;
        if (o == IROp.Load && p.code[ix].paramSeed && p.code[ix].name == sretSym()) { sret = p.code[ix].dst; }
        if (o == IROp.Nop || o == IROp.Label || (o == IROp.Load && p.code[ix].paramSeed)) { continue; }
        if (o == IROp.Call && !p.code[ix].noReturn && calls == 0) { calls = 1; res = p.code[ix].dst; continue; }
        if (isBranch(o) || o == IROp.Call || o == IROp.CallIndirect || o == IROp.Asm) { return false; }
        if (calls == 0) { own = own + 1; continue; }
        // After the call: its result returned, as it is (a copy of it, or its bytes copied to the
        // body's own result), and nothing else.
        if (o == IROp.RetVoid) { continue; }
        if (o == IROp.Ret) {
            a: Temp = p.code[ix].a;
            if (a == NO_TEMP || (a != res && a != sret)) { return false; }
            continue;
        }
        if (o == IROp.Mov && p.code[ix].a == res && res != NO_TEMP) { res = p.code[ix].dst; continue; }
        if (o == IROp.AggCopy) { continue; }
        return false;
    }
    return calls == 1 && own <= FORWARD_OWN;
}

// Whether a body can be copied into a caller of another package (`irpack`): small, and touching
// no frame slot, so the copy needs nothing renamed.
pub inlinableIR inout p:IRProgram fn:IRFunc -> bool {
    size: long = copyableSize(p, fn, false);
    return size >= 0 && size <= MAX_INLINE_INSTRS;
}

// How many instructions a body copied into a caller brings, or -1 when it cannot be copied. Two
// things stop it:
//
//   * an `asm` block that depends on where it is written (`spliceableAsm`), and any `asm` block
//     at all in a body another package will copy, whose IR carries none;
//   * a parameter's slot read or written by name (one whose address is taken), which the
//     prologue fills, and a splice has no prologue. A `str`, slice or trait-object parameter's
//     slot only holds the caller's address, and `Opt.promoteLocals` has made it a temp.
//
// A local's named slot (an aggregate, an array, a scalar whose address is taken) is renamed for
// each splice (`spliceSlot`), so it lands beside the caller's locals, never on one. With `slots`
// false those are refused too, for a body another package will copy. A hidden scratch slot
// (`AggSlot`) gets a new number for each splice (`spliceInstr`), so it lands in the caller's
// frame as one more slot, and two splices of one callee never share one (with
// `--no-splice-slots` they do, which is safe because what a callee builds there dies with the
// call, but keeps `buildWhereCopied` from building it where it is copied). An aggregate result
// (`$sret`) is a parameter like any other: the caller's argument 0 is where to write it, and the
// splice writes there.
local copyableSize inout p:IRProgram fn:IRFunc slots:bool -> long {
    if (fn.isMain || fn.instrCount == 0) { return -1; }
    if (nameOf(fn.name) == "$globalInit") { return -1; }
    real: long = 0;
    for i in 0..fn.instrCount {
        in: Instr = p.code.get(fn.firstInstr + i);
        if (in.op == IROp.Nop) { continue; }
        if (!gFreeSeedsOff && in.op == IROp.Load && in.paramSeed) { continue; }
        real = real + 1;
        if (real > MAX_SINGLE_INSTRS && real > MAX_INLINE_INSTRS) { return -1; }    // too large for either rule
        if (in.op == IROp.Load && in.paramSeed) { continue; }
        if (in.op == IROp.Asm && (!slots || !spliceableAsm(p, in))) { return -1; }
        // A `recover` statement's record and handler belong to the frame they were written in: a
        // `raise` puts back that frame's rsp and rbp.
        if (in.op == IROp.RecoverPush || in.op == IROp.FaultEdge) { return -1; }
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

// Whether an `asm` block means the same copied into another function as where it was written.
// Its operands do: each `in` is bound to a value and each `out` to a slot, which a splice maps to
// the caller's (`spliceInstr`), and the emitter moves them per use. Its text has to as well, so
// it may not:
//   * define a label (`name:`, or a bare `.name`), which a second copy in one function would
//     define again;
//   * jump, call or return (`j...`, `loop`, `call`, `ret`, `leave`, `enter`, `iret`), whose
//     target or frame is the function it was written in;
//   * name `rbp` or `rsp`, which address that function's frame.
// The rest (registers it was given, memory through them, `syscall`, `lock`, `rep movsb`) reads
// and writes the same wherever it runs. What it clobbers is unchanged too: the allocator takes an
// `asm` block for a call, so nothing lives in a caller-saved register across it, and like every
// `asm` block it leaves `r12`-`r15` and `xmm12`-`xmm14` alone.
local spliceableAsm inout p:IRProgram in:Instr -> bool {
    for k in 0..in.pieceCount {
        at: long = in.firstPiece + k;
        if (p.asmKinds.get(at) != AsmKind.Text) { continue; }
        line: str = nameOf(p.asmText.get(at));
        if (strContains(line, "rbp") || strContains(line, "rsp")) { return false; }
        i: long = 0;
        while (i < line.len && (charAt(line, i) == ' ' || charAt(line, i) == 9)) { i = i + 1; }
        e: long = i;
        while (e < line.len && charAt(line, e) != ' ' && charAt(line, e) != 9) { e = e + 1; }
        if (e == i) { continue; }
        w: str = strSlice(line, i, e - i);
        if (charAt(w, 0) == '.' || charAt(w, w.len - 1) == ':' || charAt(w, 0) == 'j') { return false; }
        if (w == "call" || w == "ret" || w == "retn" || w == "leave" || w == "enter" || w == "iret" || w == "iretq"
            || w == "loop" || w == "loope" || w == "loopne" || w == "loopz" || w == "loopnz") { return false; }
    }
    return true;
}

methods Relayout {
    // Whether function `f`'s body has a loop: a branch back to a label above it. Asked of the
    // bodies a copy is weighed for, and kept.
    loopyOf &self inout p:IRProgram f:long -> bool {
        got: long = self.loopy.get(f);
        if (got >= 0) { return got == 1; }
        fn: IRFunc = self.orig.get(f);
        self.labelStamp = self.labelStamp + 1;
        stamp: long = self.labelStamp << 32;
        found: long = 0;
        i: long = 0;
        while (i < fn.instrCount && found == 0) {
            ix: long = fn.firstInstr + i;
            o: IROp = p.code[ix].op;
            if (o == IROp.Label) { self.labelAt.put(p.code[ix].name as long, stamp + i); }
            else if (isBranch(o) && self.labelAt.getOr(p.code[ix].name as long, 0) >= stamp) { found = 1; }
            i = i + 1;
        }
        self.loopy.set(f, found);
        return found == 1;
    }

    // Per instruction of `fn`, how many loops hold it, into `d`. A loop is a branch back to a label
    // above it, and holds everything from that label to the branch: the shape the lowerer gives
    // every `while` and `for`, whose `continue` jumps back inside that span and whose `break` jumps
    // forward out of it. The loops no longer than `CLOSE_SPAN` go to `shortH`/`shortJ`. A label is
    // noted with this walk's stamp in its high half, so the table is never cleared: the lowerer's
    // label names repeat from function to function, and stay few.
    loopDepths &self inout p:IRProgram fn:IRFunc inout d:Vec<long> -> void {
        d.clear();
        self.shortH.clear();
        self.shortJ.clear();
        for i in 0..fn.instrCount + 1 { d.push(0); }
        if (gLoopInlineOff) { return; }
        self.labelStamp = self.labelStamp + 1;
        stamp: long = self.labelStamp << 32;
        for i in 0..fn.instrCount {
            ix: long = fn.firstInstr + i;
            o: IROp = p.code[ix].op;
            if (o == IROp.Label) { self.labelAt.put(p.code[ix].name as long, stamp + i); continue; }
            if (!isBranch(o)) { continue; }
            at: long = self.labelAt.getOr(p.code[ix].name as long, 0);
            if (at < stamp) { continue; }
            h: long = at - stamp;
            d.set(h, d.get(h) + 1);
            d.set(i + 1, d.get(i + 1) - 1);
            if (i - h + 1 <= CLOSE_SPAN) { self.shortH.push(h); self.shortJ.push(i); }
        }
        run: long = 0;
        for i in 0..fn.instrCount + 1 { run = run + d.get(i); d.set(i, run); }
    }

    // Per instruction of function `f`, whether the innermost loop holding it is one of the short
    // loops `loopDepths` found and every call in that loop is one a copy takes away, slow paths
    // aside (`takenAway`). With no call left on its fast path, what such a loop holds stays in
    // registers, which is worth a larger copy (`CLOSE_INSTRS`) than a call-free one anywhere else.
    // `ok` is left empty when the function has no short loop.
    closableLoops &self inout p:IRProgram f:long fn:IRFunc inout ok:Vec<bool> -> void {
        ok.clear();
        if (self.shortH.len() == 0) { return; }
        best: Vec<long>;
        for i in 0..fn.instrCount { ok.push(false); best.push(NO_SPAN); }
        for q in 0..self.shortH.len() {
            h: long = self.shortH.get(q);
            j: long = self.shortJ.get(q);
            good: bool = true;
            i: long = h;
            while (good && i <= j) { good = self.takenAway(p, f, fn, i); i = i + 1; }
            for k in h..j + 1 {
                if (best.get(k) > j - h + 1) { best.set(k, j - h + 1); ok.set(k, good); }
            }
        }
    }

    // Whether instruction `i` of function `f` leaves no call on a loop's fast path once copies are
    // made: no call at all; a call that never returns; a call to a body whose leading early return
    // is copied in its place (`spliceGuard`); or a call to a body whose copy, slow paths set aside,
    // makes no call (`callFree`), has no loop, and fits `CLOSE_INSTRS`.
    takenAway &self inout p:IRProgram f:long fn:IRFunc i:long -> bool {
        ix: long = fn.firstInstr + i;
        o: IROp = p.code[ix].op;
        if (o == IROp.CallIndirect || o == IROp.Asm) { return false; }
        if (o != IROp.Call || p.code[ix].noReturn) { return true; }
        if (i + 1 < fn.instrCount && p.code[ix + 1].op == IROp.FaultEdge) { return false; }
        in: Instr = p.code.get(ix);
        g: long = self.calleeAt(in);
        if (g < 0 || g == f) { return false; }
        if (self.guardTarget(p, in) == g) { return true; }
        c: long = self.callFree(p, g, MAX_INLINE_DEPTH - 1, true);
        return c >= 0 && c <= CLOSE_INSTRS && !self.cfLoop.get(cfKey(g, MAX_INLINE_DEPTH - 1, true));
    }

    // The function a direct call names, when this pass could copy it there (the argument count
    // matches its parameter seeds), or -1.
    calleeAt &self in:Instr -> long {
        if (in.op != IROp.Call || in.name == NO_SYM) { return -1; }
        hit: Option<long> = self.fnOf.find(in.name as long);
        at: long = -1;
        match hit { Some(x) { at = x; } None { return -1; } }
        if (self.seeds.get(at) != in.argCount) { return -1; }
        return at;
    }

    // The size of a copy of body `g` with every call in it copied in turn, at most `levels` deep,
    // or -1 when some call would stay one: an indirect call, an `asm` block, a `memcpy`, a call to
    // a body that cannot be copied or to `g` itself. A call that never returns does not count:
    // nothing is live across it (`RegAlloc.computeIntervals`), and it is the cold end of a check.
    // With `guarded`, the slow paths are set aside: a call to a body whose leading early return is
    // copied in its place (`spliceGuard`) counts as that test, and a `memcpy` as free (it is moves
    // where its length is a small constant). Whether the copy has a loop goes to `cfLoop`.
    callFree &self inout p:IRProgram g:long levels:long guarded:bool -> long {
        key: long = cfKey(g, levels, guarded);
        got: long = self.cfMemo.get(key);
        if (got != CF_UNKNOWN) { return got; }
        total: long = self.sizes.get(g);
        lp: bool = total >= 0 && self.loopyOf(p, g);
        fn: IRFunc = self.orig.get(g);
        i: long = 0;
        while (total >= 0 && i < fn.instrCount) {
            ix: long = fn.firstInstr + i;
            i = i + 1;
            o: IROp = p.code[ix].op;
            if (o == IROp.MemCopy && guarded) { continue; }
            if (o == IROp.CallIndirect || o == IROp.Asm || o == IROp.MemCopy) { total = -1; continue; }
            if (o != IROp.Call || p.code[ix].noReturn) { continue; }
            in: Instr = p.code.get(ix);
            h: long = self.calleeAt(in);
            if (guarded && h >= 0 && self.guardTarget(p, in) == h) {
                total = total + self.guards.get(h) + 3;
                continue;
            }
            if (h < 0 || h == g || levels == 0) { total = -1; continue; }
            c: long = self.callFree(p, h, levels - 1, guarded);
            if (c < 0) { total = -1; continue; }
            if (self.cfLoop.get(cfKey(h, levels - 1, guarded))) { lp = true; }
            total = total + c;
            if (total > MAX_SINGLE_INSTRS) { total = -1; }
        }
        self.cfMemo.set(key, total);
        self.cfLoop.set(key, lp);
        return total;
    }
}

// Whether the call at `k` sits on a path that ends in a call that never returns, with no label
// or branch between: building the message for a `fail`, which runs at most once. A body copied
// there saves nothing worth its bytes.
local towardNever inout p:IRProgram fn:IRFunc k:long -> bool {
    j: long = k + 1;
    while (j < fn.instrCount) {
        o: IROp = p.code[fn.firstInstr + j].op;
        if (o == IROp.Call && p.code[fn.firstInstr + j].noReturn) { return true; }
        if (o == IROp.Label || o == IROp.Jmp || o == IROp.Jcc || o == IROp.Jz || o == IROp.Ret
            || o == IROp.RetVoid || o == IROp.CallIndirect || o == IROp.Asm) { return false; }
        j = j + 1;
    }
    return false;
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
            while (k < fn.instrCount && p.code[fn.firstInstr + k].op == IROp.Nop) { k = k + 1; }
            if (k >= fn.instrCount || p.code[fn.firstInstr + k].op != IROp.RetVoid) { return -1; }
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

// Whether `in` may sit between an accumulated call and its operator: arithmetic on temps that
// neither reads the call's result `t` nor can fault, so it runs the same before the call's work
// as after it.
local betweenOk in:Instr t:Temp -> bool {
    o: IROp = in.op;
    if (!(o == IROp.Const || o == IROp.Mov || o == IROp.Add || o == IROp.Sub || o == IROp.Mul
          || o == IROp.BAnd || o == IROp.BOr || o == IROp.BXor || o == IROp.Shl || o == IROp.Shr
          || o == IROp.BNot || o == IROp.Convert)) { return false; }
    if (in.dst == NO_TEMP || in.a == t || (!in.bIsImm && in.b == t)) { return false; }
    return true;
}

// Whether `t` is the temp a parameter's seed defines.
local isSeedTemp inout p:IRProgram fn:IRFunc t:Temp -> bool {
    if (t == NO_TEMP) { return false; }
    for i in 0..fn.instrCount {
        s: Instr = p.code.get(fn.firstInstr + i);
        if (s.op == IROp.Nop) { continue; }
        if (!(s.op == IROp.Load && s.paramSeed)) { return false; }
        if (s.dst == t) { return true; }
    }
    return false;
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
// (`Result.unwrap`, `Try.output`) is the common case: without this, every such method would
// stay a call.
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
        hit: Option<long> = self.fnOf.find(in.name as long);
        at: long = -1;
        match hit { Some(x) { at = x; } None { return -1; } }
        if (at == caller) { return -1; }
        if (!self.canInline.get(at)) { return -1; }
        if (self.seeds.get(at) != in.argCount) { return -1; }
        return at;
    }

    // The leading run of parameter seeds, which is how many arguments the body expects. A body
    // whose seeds are not its leading run is not one this pass understands, and is left alone.
    // Read in place; a callee's is asked once (`seeds`).
    seedCount &self inout p:IRProgram fn:IRFunc -> long {
        n: long = 0;
        i: long = 0;
        while (i < fn.instrCount) {
            ix: long = fn.firstInstr + i;
            i = i + 1;
            o: IROp = p.code[ix].op;
            if (o == IROp.Nop) { continue; }
            if (o == IROp.Load && p.code[ix].paramSeed) { n = n + 1; continue; }
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
        hit: Option<long> = self.fnOf.find(in.name as long);
        g: long = -1;
        match hit { Some(x) { g = x; } None { return -1; } }
        if (self.guards.get(g) < 0) { return -1; }
        if (self.seeds.get(g) != in.argCount) { return -1; }
        return g;
    }

    // `f(args)`, where f begins `if (test) { return; }` (as `guardEnd` found), becomes the test,
    // copied here over the arguments, and the call only when the test would not return at once:
    //
    //     <the test's loads and arithmetic>; jcc .GDn if !test; call f(args); .GDn:
    //
    // The test is pure (loads and arithmetic on the parameters) and runs just where the callee
    // would have run it first thing, so it sees what the callee would. The callee tests again,
    // which changes nothing. What `Vec.push` pays for its growth check is then a compare, not a
    // call.
    spliceGuard &self inout p:IRProgram g:long call:Instr via:long -> void {
        fn: IRFunc = self.orig.get(g);
        self.spliceSeq = self.spliceSeq + 1;
        self.labelSeq = self.labelSeq + 1;
        outer: long = self.curSeq;
        self.curSeq = self.spliceSeq;
        done: Sym = madeName(".GD", self.labelSeq, "");
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
        endL: Sym = madeName(".IE", self.curLabel, "");
        depth0: long = self.curDepth;
        bodyDepths: Vec<long>;
        if (!gLoopInlineOff && self.loopyOf(p, at)) { self.loopDepths(p, fn, &bodyDepths); }

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
                // How many loops hold it: those around this splice, and the body's own.
                here: long = depth0;
                if (bodyDepths.len() > 0) { here = depth0 + bodyDepths.get(i - 1); }
                // In a call-free copy, every call (`callFree` found each one copyable), but where
                // a callee's leading early return is copied in its place.
                if (self.forceNest && !in.noReturn && !(self.forceGuard && self.guardTarget(p, in) >= 0)) {
                    inner: long = self.calleeAt(in);
                    for s in self.stack { if (s == inner) { inner = -1; } }
                    if (inner >= 0 && inner != self.topCaller) {
                        self.curDepth = here;
                        self.splice(p, inner, in, self.curSeq);
                        self.curDepth = depth0;
                        continue;
                    }
                }
                inner: long = self.nestedTarget(p, in);
                if (inner >= 0 && self.sites.get(inner) > 1 && towardNever(p, fn, i - 1)) { inner = -1; }
                // Within the budget of the top-level splice it sits in; but a body that only hands
                // its call on (`forwardingBody`) brings its callee's size and little of its own, so
                // the callee is copied as a call to it would be.
                if (inner >= 0 && (self.code.len() - self.spliceStart) + self.sizes.get(inner) > self.nestBudget
                    && !(self.forwards.get(at) && self.sizes.get(inner) <= MAX_INLINE_INSTRS)) { inner = -1; }
                if (inner >= 0) {
                    self.curDepth = here;
                    self.splice(p, inner, in, self.curSeq);
                    self.curDepth = depth0;
                    continue;
                }
                // In a loop, past the budget, a body whose copy makes no call (`callFree`), its own
                // calls copied in turn: what the loop holds across the call it replaces then stays
                // in registers. A copy that still called would cost the loop more than the call
                // did: every value live across a call in a loop needs one of the four registers a
                // call keeps, or the frame. Copies that keep calls, larger copies and copies with
                // loops were each tried here, and each made this compiler compiling itself slower.
                if (!self.forceNest && !gLoopInlineOff && here >= 1) {
                    g: long = self.calleeAt(in);
                    for s in self.stack { if (s == g) { g = -1; } }
                    if (g >= 0 && g != self.topCaller) {
                        lv: long = MAX_INLINE_DEPTH - 1 - self.stack.len();
                        c: long = self.callFree(p, g, lv, false);
                        if (c >= 0 && c <= MAX_INLINE_INSTRS && !self.cfLoop.get(cfKey(g, lv, false))) {
                            self.curDepth = here;
                            self.forceNest = true;
                            self.splice(p, g, in, self.curSeq);
                            self.forceNest = false;
                            self.curDepth = depth0;
                            self.nCallFree = self.nCallFree + 1;
                            continue;
                        }
                    }
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
        s: String;
        s.pushStr(nameOf(n));
        s.pushStr("$i");
        s.pushLong(self.curLabel);
        made: Sym = internString(s);
        p.noteSlot(made, p.slotBytesOf(n));
        // In the caller's frame, as wide as the callee's own declaration of it.
        if (self.topCaller >= 0 && self.stack.len() > 0) {
            p.noteFnSlot(self.orig.get(self.topCaller).name, made, p.fnSlotBytesOf(self.orig.get(self.stack.last()).name, n));
        }
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
        // A scratch slot of this splice's own: what one copy builds there then dies with that
        // copy, and a later pass may build it where it is copied (`buildWhereCopied`) without
        // another copy's use of the same slot in the way.
        if (in.op == IROp.AggSlot && !gSpliceSlotsOff) {
            key: long = self.curSeq * 4194304 + in.imm;
            hit: Option<long> = self.amap.find(key);
            match hit {
                Some(s) { out.imm = s; }
                None {
                    made: long = p.addAggSlot(p.aggSlots.get(in.imm));
                    self.amap.put(key, made);
                    out.imm = made;
                }
            }
        }
        if (in.argCount > 0) {
            out.firstArg = self.args.len();
            for k in 0..in.argCount {
                self.args.push(self.spliceTemp(p, p.args.get(in.firstArg + k)));
            }
        }
        // An `asm` block (`spliceableAsm`): its inputs are this splice's temps, and an output
        // goes to the slot renamed for this splice, which the body's later read of it names too.
        if (in.pieceCount > 0) {
            out.firstPiece = self.aVals.len();
            for k in 0..in.pieceCount {
                j: long = in.firstPiece + k;
                nm: Sym = p.asmNames.get(j);
                if (p.asmKinds.get(j) == AsmKind.Out && nm != NO_SYM) { nm = self.spliceSlot(p, nm); }
                self.aKinds.push(p.asmKinds.get(j));
                self.aRegs.push(p.asmRegs.get(j));
                self.aNames.push(nm);
                self.aVals.push(self.spliceTemp(p, p.asmVals.get(j)));
                self.aText.push(p.asmText.get(j));
                self.aSizes.push(p.asmSizes.get(j));
            }
        }
        self.code.push(out);
    }

    spliceLabel &self n:Sym -> Sym {
        if (n == NO_SYM) { return n; }
        hit: Option<Sym> = self.lmap.find(n as long);
        match hit { Some(m) { return m; } None { } }
        made: Sym = madeNameLabel(self.curLabel, n);
        self.lmap.put(n as long, made);
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

// `.IL<site>_<label>`: a spliced body's label at one site.
local madeNameLabel site:long n:Sym -> Sym {
    s: String;
    s.pushStr(".IL");
    s.pushLong(site);
    s.push('_');
    s.pushStr(nameOf(n));
    return internString(s);
}
