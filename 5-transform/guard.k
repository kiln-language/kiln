// The immutability guard: a global not declared `var` is never written after the compiler
// computed it.
//
// A write is more than an assignment, so this first decides, per function, which by-reference
// parameters a body writes through (a fixpoint over the call graph), then holds every use of a
// const to it. What escapes into `unsafe` faults instead: a const is emitted in `.rodata`.
#include <support::compiler>
#include <parse::{ast, registry, types, upstream}>
#include <{eval, facts}>
#include <stdlib::{fmt, io, map, mem, option, string, time, vec}>

local WRITES_ALL: long = 4611686018427387904;   // bit 62: a store through a raw pointer, or `asm`

pub struct ConstGuard {
    fnAt: HashMap<str, long>,      // resolved name -> `fns` index
    writes: Vec<long>,             // per function: bit k = writes through parameter k
    paramIx: HashMap<str, long>,   // the function being scanned: parameter name -> index
    mask: long,                    // and the bits found so far
    changed: bool,
    // In a package build: which parameters each function hands, through calls, to a trait
    // dispatch, and where. Whether such a call writes depends on every implementation in the
    // final program, which a dependent may add to, so it is written into the facts for the
    // dependent to answer again. A chain per function through flat arrays.
    cur: long,
    deps: Vec<DepFact>,
    depNext: Vec<long>,
    depHead: Vec<long>,
    depKeys: HashMap<str, bool>,
    // A borrow local the checker bound to a place (`r = &subject.$V$k`, a match through a
    // borrow): writing through it writes that place, so its root is the place's root.
    alias: HashMap<str, NodeId>,
    // The `for x in xs` whose body `holdLoop` is reading: its variable, whether that is a borrow
    // (a struct element), whether the loop lends `xs` (`for x in &xs`), and `xs` as a path.
    hx: Sym,
    hRef: bool,
    hLend: bool,
    hPath: Vec<Sym>,
    hShown: str,                   // and `xs` as the source spells it, for the messages
    hFn: long,                     // the function whose loops are being held
    // Whether a function writes a `var` global by name, itself or through what it calls, asked
    // only of the globals a loop walks or a borrowed match arm holds, and only of the functions
    // that loop or arm reaches (`reachesWrite`). Each reached function's body is read once for
    // the globals it writes and the functions it calls (`gfInfo`); each answer is kept per global
    // (`gfMemo`). A call through a fn value reaches any function whose address the program takes
    // (`gAddressedFns`, which the checker noted).
    gfState: Vec<bool>,            // per function: its body has been read
    gfWHead: Vec<long>,            // its directly written globals, a chain through `gfW`
    gfW: Vec<Sym>,
    gfWNext: Vec<long>,
    gfCHead: Vec<long>,            // its callees (-1: any addressed function), a chain through `gfC`
    gfC: Vec<long>,
    gfCNext: Vec<long>,
    gfCur: long,
    gfAddr: Vec<long>,             // the addressed functions, by index, once asked
    gfAddrDone: bool,
    gfMemoAt: HashMap<str, long>,  // per global, where its run of `gfMemo` starts
    gfMemo: Vec<long>,             // 0 unknown, 1 writes, 2 does not, 3 met in the current query
    gfTouched: Vec<long>,          // what the current query marked 3
    gfUs: long,                    // time spent answering, for `--time-phases`
    hGlobal: Sym,                  // the `var` global a loop being held walks, or NO_SYM
    // Below each bit of `writes`, which fields of that parameter the function writes, asked only for
    // a call a held loop's body makes (`calleePaths`) and kept once answered: a chain per function
    // of (parameter, path) entries, the path the fields' names joined by `.` (`cur.name`), or ""
    // for the whole parameter. What lets `self.err()` inside `for a in self.cur.attrs` count as
    // writing `self.errors` and not all of `self`. A path is cut at the first step that is not a
    // field (an element, a call's borrow, a dereference) and at WP_DEPTH fields: a shorter path
    // stands for everything under it, so cutting only ever claims more. A callee met while its own
    // answer is being worked out (recursion) answers "all of it".
    wpHead: Vec<long>,
    wpParam: Vec<long>,
    wpPath: Vec<Sym>,
    wpNext: Vec<long>,
    wpDone: Vec<long>,             // per function: bit k = parameter k's paths are known
    wpBusy: Vec<long>,             // per function: bit k = being worked out
    wpStackF: Vec<long>,           // what is being worked out, innermost last
    wpStackP: Vec<long>,
    wpNeedF: long,                 // the walk stopped for this callee's answer (-1: it did not)
    wpNeedP: long,
    wpTarget: long,                // the parameter the walk is for
    wpOut: Vec<Sym>,               // and what it found
    wpIx: HashMap<str, long>,      // the walked function's parameters, as `paramIx`
    wpAlias: HashMap<str, NodeId>, // and its borrow locals, as `alias`
    ppCut: bool,                   // `paramPlace` stopped at a step that is not a field
    ppDepth: long                  // and how many fields it named
}

local WP_DEPTH: long = 3;

methods ConstGuard for Default {
    new -> ConstGuard {
        return ConstGuard { fnAt: map![], writes: vec![], paramIx: map![], mask: 0, changed: false,
                            cur: -1, deps: vec![], depNext: vec![], depHead: vec![], depKeys: map![],
                            alias: map![], hx: NO_SYM, hRef: false, hLend: false, hPath: vec![], hShown: "", hFn: -1,
                            gfState: vec![], gfWHead: vec![], gfW: vec![], gfWNext: vec![], gfCHead: vec![],
                            gfC: vec![], gfCNext: vec![], gfCur: -1, gfAddr: vec![], gfAddrDone: false,
                            gfMemoAt: map![], gfMemo: vec![], gfTouched: vec![], gfUs: 0, hGlobal: NO_SYM,
                            wpHead: vec![], wpParam: vec![], wpPath: vec![], wpNext: vec![], wpDone: vec![],
                            wpBusy: vec![], wpStackF: vec![], wpStackP: vec![], wpNeedF: -1, wpNeedP: 0,
                            wpTarget: -1, wpOut: vec![], wpIx: map![], wpAlias: map![], ppCut: false,
                            ppDepth: 0 };
    }
}

methods ConstGuard {
    run &self inout a:Ast page:long -> void {
        self.index(a);
        rounds: long = 0;
        self.changed = true;
        while (self.changed && rounds < 64) {
            self.changed = false;
            for i in 0..a.fns.len() {
                if (!a.fns.get(i).isTemplate) { self.scanFunction(a, i); }
            }
            rounds = rounds + 1;
        }
        self.holdSelfLends(a);
        self.holdArms(a);
        n: long = a.blockLen(page);
        hold: Instant = monotonic();
        for k in 0..n {
            st: Stmt = a.stmtAt(page, k);
            gPos = a.stmtPos.get(a.stmtIdAt(page, k));
            // A dependency's bodies and initializers were held to this by its own compile.
            if (st.kind == StmtKind.FunctionDef && !a.fns.get(st.at).isTemplate
                && a.fns.get(st.at).body >= 0 && !isExternFn(st.at) && !isUnchecked(st.at)) {
                self.guardGuarded(a, st.at);
            }
            if (st.kind == StmtKind.VarDecl && !isExternGlobal(a.decls.get(st.at).name)) {
                self.guardExpr(a, a.decls.get(st.at).init);
            }
        }
        if (gTimePhases) {
            read: long = 0;
            for r in self.gfState { if (r) { read = read + 1; } }
            eprintln("  holding: {} ms; global writes: {} ms, {} bodies read for {} global(s)", elapsedUs(hold) / 1000,
                     self.gfUs / 1000, read, self.gfMemoAt.len());
        }
    }

    // A `&self` call on the place a borrowed match arm holds the payload of (`gSelfLends`): a
    // read-only lend unless the method writes `self`, and then the write could release what the
    // binding points at. Refused here, where the write masks are known.
    holdSelfLends &self inout a:Ast -> void {
        for k in 0..gSelfLends.len() {
            s: SelfLend = gSelfLends.get(k);
            if (s.callee < 0 || s.callee >= self.writes.len()) { continue; }
            w: long = self.writes.get(s.callee);
            if (w == WRITES_ALL || (w & 1) != 0) {
                gPos = s.pos;
                enterFn(s.fnName);
                failStr(format("'{}' is lent mutably in {} while a match arm holds '{}', a borrow of the matched value's payload -- '{}' writes `self`, and the write could release what '{}' points at; finish with the borrow first, or match on a clone",
                               s.what, nameOf(s.fnName), nameOf(s.made), nameOf(a.fns.get(s.callee).name), nameOf(s.made)));
            }
        }
        gSelfLends.clear();
    }

    // A borrowed match arm over a `var` global (`gHeldArms`): nothing it calls may write the global,
    // which would release or move what the arm's binding points at.
    holdArms &self inout a:Ast -> void {
        if (gHeldArms.len() == 0) { return; }
        for h in gHeldArms {
            hit: Sym = self.writingCall(a, h.body, h.global);
            if (hit != NO_SYM) {
                gPos = h.pos;
                enterFn(h.fnName);
                failStr(format("'{}' is written by '{}', which {} calls while a match arm holds '{}', a borrow into it -- the write could release or move what '{}' points at; finish with the borrow first, or match on a clone",
                               lastComponentOf(nameOf(h.global)), nameOf(hit), nameOf(h.fnName), nameOf(h.made), nameOf(h.made)));
            }
        }
        gHeldArms.clear();
    }

    // The first call in block `b` (or anything it holds) whose callee writes global `bit`.
    writingCall &self inout a:Ast b:long bit:Sym -> Sym {
        if (b < 0) { return NO_SYM; }
        for k in 0..a.blockLen(b) {
            st: Stmt = a.stmtAt(b, k);
            exprs: Vec<NodeId> = stmtExprs(a, st);
            for e in exprs {
                hit: Sym = self.writingCallIn(a, e, bit);
                if (hit != NO_SYM) { return hit; }
            }
            kids: Vec<long> = childBlocks(a, st);
            for j in 0..kids.len() {
                hk: Sym = self.writingCall(a, kids.get(j), bit);
                if (hk != NO_SYM) { return hk; }
            }
        }
        return NO_SYM;
    }
    writingCallIn &self inout a:Ast id:NodeId bit:Sym -> Sym {
        if (id == NO_NODE) { return NO_SYM; }
        e: Expr = a.expr(id);
        if (e.left != NO_NODE || e.right != NO_NODE) {
            l: Sym = self.writingCallIn(a, e.left, bit);
            if (l != NO_SYM) { return l; }
            return self.writingCallIn(a, e.right, bit);
        }
        p: Payload = e.payload;
        match p {
            Call(i) {
                c: CallNode = a.calls.get(i);
                if (self.callWritesGlobal(a, c, bit)) { return intern(calledName(c)); }
                r: Sym = self.writingCallIn(a, c.receiver, bit);
                if (r != NO_SYM) { return r; }
                for k in 0..c.argCount {
                    x: Sym = self.writingCallIn(a, a.argAt(c, k), bit);
                    if (x != NO_SYM) { return x; }
                }
                return self.writingCallIn(a, c.callee, bit);
            }
            Sub(v) { return self.writingCallIn(a, v, bit); }
            Field(f) { return self.writingCallIn(a, a.fields.get(f).base, bit); }
            Index(i) {
                ix: IndexNode = a.indexes.get(i);
                bb: Sym = self.writingCallIn(a, ix.base, bit);
                if (bb != NO_SYM) { return bb; }
                return self.writingCallIn(a, ix.index, bit);
            }
            Lit(i) {
                ln: LitNode = a.lits.get(i);
                for k in 0..ln.initCount {
                    v: Sym = self.writingCallIn(a, a.inits.get(ln.firstInit + k).value, bit);
                    if (v != NO_SYM) { return v; }
                }
                return self.writingCallIn(a, ln.rest, bit);
            }
            _ { }
        }
        return NO_SYM;
    }

    // --- which `var` globals a function writes ------------------------------------------

    // Whether a call may write global `g` by name: its function, any implementation a dispatch
    // reaches, any addressed function for a call through a fn value or a fn-typed field.
    callWritesGlobal &self inout a:Ast c:CallNode g:Sym -> bool {
        if (c.slot == SLOT_FNPTR || c.callee != NO_NODE) { return self.reachesWrite(a, -1, g); }
        if (c.slot != NO_SLOT) {
            ts: Vec<long> = self.dispatchTargets(a, c);
            for t in ts { if (self.reachesWrite(a, t, g)) { return true; } }
            return false;
        }
        hit: Option<long> = self.fnAt.find(nameOf(c.name));
        match hit { Some(i) { return self.reachesWrite(a, i, g); } None { } }
        return false;
    }

    // Every implementation a dispatch `c` may reach.
    dispatchTargets &self inout a:Ast c:CallNode -> Vec<long> {
        out: Vec<long>;
        trait: Sym = a.expr(c.receiver).structName;
        for i in 0..gReg.implCount() {
            im: TraitImplDef = gReg.implAt(i);
            if (intern(gReg.traitMangled(im.trait)) != trait) { continue; }
            ti: long = gReg.findTrait(nameOf(im.trait.name));
            if (ti < 0) { continue; }
            t: TraitDef = gReg.traitDef(ti);
            if (c.slot < 0 || c.slot >= t.methodCount) { continue; }
            hit: Option<long> = self.fnAt.find(nameOf(implMethodName(im, gReg.traitMethodAt(t, c.slot).name)));
            match hit { Some(fi) { out.push(fi); } None { } }
        }
        return out;
    }

    // Does function `f` (-1: any addressed function) write `g` by name, itself or through what it
    // calls? A depth-first walk of the calls from `f`, each function's body read once. A walk that
    // finds no writer has seen everything reachable from where it started, so every function it
    // met writes nothing of `g`; one that finds one knows that only of the functions on its path,
    // and forgets what else it met (a function in a cycle can have been cut short there).
    reachesWrite &self inout a:Ast f:long g:Sym -> bool {
        if (self.gfState.len() == 0) {
            for i in 0..a.fns.len() {
                self.gfState.push(false); self.gfWHead.push(-1); self.gfCHead.push(-1);
            }
        }
        base: long = -1;
        hit: Option<long> = self.gfMemoAt.find(nameOf(g));
        match hit { Some(b) { base = b; } None { } }
        if (base < 0) {
            base = self.gfMemo.len();
            for i in 0..a.fns.len() { self.gfMemo.push(0); }
            self.gfMemoAt.put(nameOf(g), base);
        }
        self.gfTouched.clear();
        t0: Instant = Instant { secs: 0, nanos: 0 };
        if (gTimePhases) { t0 = monotonic(); }
        found: bool = self.reachFrom(a, f, g, base);
        if (gTimePhases) { self.gfUs = self.gfUs + elapsedUs(t0); }
        for k in 0..self.gfTouched.len() {
            t: long = self.gfTouched.get(k);
            if (self.gfMemo.get(base + t) == 3) {
                if (found) { self.gfMemo.set(base + t, 0); } else { self.gfMemo.set(base + t, 2); }
            }
        }
        self.gfTouched.clear();
        return found;
    }
    reachFrom &self inout a:Ast f:long g:Sym base:long -> bool {
        if (f < 0) {
            self.ensureAddressed(a);
            for k in 0..self.gfAddr.len() { if (self.reachFrom(a, self.gfAddr.get(k), g, base)) { return true; } }
            return false;
        }
        m: long = self.gfMemo.get(base + f);
        if (m == 1) { return true; }
        if (m != 0) { return false; }
        self.gfMemo.set(base + f, 3);
        self.gfTouched.push(f);
        self.gfInfo(a, f);
        w: long = self.gfWHead.get(f);
        while (w >= 0) {
            if (self.gfW.get(w) == g) { self.gfMemo.set(base + f, 1); return true; }
            w = self.gfWNext.get(w);
        }
        c: long = self.gfCHead.get(f);
        while (c >= 0) {
            if (self.reachFrom(a, self.gfC.get(c), g, base)) { self.gfMemo.set(base + f, 1); return true; }
            c = self.gfCNext.get(c);
        }
        return false;
    }

    // The functions whose address the program takes, by index.
    ensureAddressed &self inout a:Ast -> void {
        if (self.gfAddrDone) { return; }
        self.gfAddrDone = true;
        seen: HashMap<str, bool>;
        for n in gAddressedFns {
            if (seen.has(nameOf(n))) { continue; }
            seen.put(nameOf(n), true);
            hit: Option<long> = self.fnAt.find(nameOf(n));
            match hit { Some(fi) { self.gfAddr.push(fi); } None { } }
        }
    }

    // Function `f`'s body, read once: the `var` globals it writes by name and what it calls. A
    // dependency's function names no global of this package (it cannot include it) and is taken
    // to write none.
    gfInfo &self inout a:Ast f:long -> void {
        if (self.gfState.get(f)) { return; }
        self.gfState.set(f, true);
        fn: FnNode = a.fns.get(f);
        if (fn.isTemplate || fn.body < 0 || isExternFn(f) || isUnchecked(f)) { return; }
        // The borrow locals of the function being held, put back after: this runs in the middle
        // of holding one.
        saved: HashMap<str, NodeId> = map![];
        swapValues(&saved, &self.alias);
        wasCur: long = self.gfCur;
        self.gfCur = f;
        self.gwBlock(a, fn.body);
        self.gfCur = wasCur;
        swapValues(&saved, &self.alias);
    }

    gwMark &self inout a:Ast place:NodeId -> void {
        path: Vec<Sym>;
        if (!self.holdPath(a, place, NO_SYM, &path) || path.len() == 0) { return; }
        self.gwMarkName(a, path.get(0));
    }
    gwMarkName &self inout a:Ast n:Sym -> void {
        if (!isVarGlobalName(n)) { return; }
        self.gfW.push(n);
        self.gfWNext.push(self.gfWHead.get(self.gfCur));
        self.gfWHead.set(self.gfCur, self.gfW.len() - 1);
    }
    gwEdge &self to:long -> void {
        self.gfC.push(to);
        self.gfCNext.push(self.gfCHead.get(self.gfCur));
        self.gfCHead.set(self.gfCur, self.gfC.len() - 1);
    }

    gwBlock &self inout a:Ast b:long -> void {
        if (b < 0) { return; }
        for k in 0..a.blockLen(b) {
            st: Stmt = a.stmtAt(b, k);
            if (st.kind == StmtKind.VarDecl) { self.forgetAlias(a.decls.get(st.at).name); }
            if (st.kind == StmtKind.With) { self.gwMarkName(a, a.withs.get(st.at).name); }
            if (st.kind == StmtKind.Asm) {
                n: AsmNode = a.asms.get(st.at);
                for j in 0..n.pieceCount {
                    pc: AsmPiece = a.asmPieces.get(n.firstPiece + j);
                    if (pc.kind == AsmKind.In) { self.gwMark(a, pc.value); }
                    if (pc.kind == AsmKind.Out) { self.gwMarkName(a, pc.name); }
                }
            }
            exprs: Vec<NodeId> = stmtExprs(a, st);
            for e in exprs { self.gwExpr(a, e); }
            kids: Vec<long> = childBlocks(a, st);
            for j in 0..kids.len() { self.gwBlock(a, kids.get(j)); }
        }
    }

    gwExpr &self inout a:Ast id:NodeId -> void {
        if (id == NO_NODE) { return; }
        e: Expr = a.expr(id);
        if (e.op == Op.Assignment) {
            if (!self.noteAlias(a, e)) { self.gwMark(a, e.left); }
            self.gwExpr(a, e.left);
            self.gwExpr(a, e.right);
            return;
        }
        if (e.left != NO_NODE) { self.gwExpr(a, e.left); self.gwExpr(a, e.right); return; }
        if (e.op == Op.AddressOf) {
            p: Payload = e.payload;
            match p {
                Sub(v) {
                    if (e.kind != Lit.Fn) { self.gwMark(a, v); }
                    self.gwExpr(a, v);
                }
                _ { }
            }
            return;
        }
        if (e.op == Op.FunctionCall || e.op == Op.MethodCall) {
            c: CallNode = a.calls.get(0);
            match e.payload { Call(i) { c = a.calls.get(i); } _ { } }
            nodes: Vec<NodeId>;
            if (c.receiver != NO_NODE) { nodes.push(c.receiver); }
            for k in 0..c.argCount { nodes.push(a.argAt(c, k)); }
            for k in 0..nodes.len() {
                self.gwExpr(a, nodes.get(k));
                if (!strWord(a, nodes.get(k)) && self.calleeWrites(a, c, k)) { self.gwMark(a, nodes.get(k)); }
            }
            self.gwExpr(a, c.callee);
            if (c.slot == SLOT_FNPTR || c.callee != NO_NODE) { self.gwEdge(-1); return; }
            if (c.slot != NO_SLOT) {
                ts: Vec<long> = self.dispatchTargets(a, c);
                for t in ts { self.gwEdge(t); }
                return;
            }
            hit: Option<long> = self.fnAt.find(nameOf(c.name));
            match hit { Some(fi) { self.gwEdge(fi); } None { } }
            return;
        }
        p2: Payload = e.payload;
        match p2 {
            Sub(v)   { self.gwExpr(a, v); }
            Field(i) { self.gwExpr(a, a.fields.get(i).base); }
            Index(i) {
                ix: IndexNode = a.indexes.get(i);
                self.gwExpr(a, ix.base); self.gwExpr(a, ix.index);
                self.gwExpr(a, ix.sliceStart); self.gwExpr(a, ix.sliceEnd);
            }
            Lit(i) {
                ln: LitNode = a.lits.get(i);
                for k in 0..ln.initCount { self.gwExpr(a, a.inits.get(ln.firstInit + k).value); }
                self.gwExpr(a, ln.rest);
            }
            _ { }
        }
    }

    // One function held to immutability and to what its loops lend, under a recovery point
    // (`armRecovery`): every function's first error is reported, and the driver stops after the
    // phase (`stopIfErrors`).
    guardGuarded &self inout a:Ast at:long -> void {
        enterFn(a.fns.get(at).name);
        if (!canRecover()) { self.guardOne(a, at); return; }
        hit: long = 0;
        unsafe { hit = armRecovery(); }
        if (hit != 0) { return; }
        self.guardOne(a, at);
        disarmRecovery();
    }
    guardOne &self inout a:Ast at:long -> void {
        self.alias.clear();
        self.guardBlock(a, a.fns.get(at).body);
        self.holdFunction(a, at);
    }

    index &self inout a:Ast -> void {
        self.fnAt.clear();
        self.writes.clear();
        self.depHead.clear();
        self.wpHead.clear();
        self.wpDone.clear();
        self.wpBusy.clear();
        self.wpParam.clear();
        self.wpPath.clear();
        self.wpNext.clear();
        for i in 0..a.fns.len() {
            f: FnNode = a.fns.get(i);
            if (!f.isTemplate) { self.fnAt.put(nameOf(f.name), i); }
            w: long = 0;
            if (isExternFn(i)) {
                fi: long = fnFactOf(i);
                if (fi >= 0) { w = gFacts.fns.get(fi).writes; } else { w = WRITES_ALL; }
            }
            // A lazy method nothing here checked: its body says nothing yet, so it is taken to
            // write everything, which only a dispatch could ever ask (a call would have checked it).
            else if (isUnchecked(i)) { w = WRITES_ALL; }
            self.writes.push(w);
            self.depHead.push(-1);
            self.wpHead.push(-1);
            self.wpDone.push(0);
            self.wpBusy.push(0);
        }
    }

    // What this compile decided `at` writes through: the mask, and the dispatches whose answer a
    // dependent has to give again. For the facts a package build writes.
    writesOf &self at:long -> long { return self.writes.get(at); }
    depsOf &self at:long -> Vec<DepFact> {
        out: Vec<DepFact>;
        d: long = self.depHead.get(at);
        while (d >= 0) { out.push(self.deps.get(d)); d = self.depNext.get(d); }
        return out;
    }

    addDep &self param:long trait:Sym slot:long pos:long -> void {
        if (self.cur < 0 || trait == NO_SYM) { return; }
        key: String = format("{}|{}|{}|{}|{}", self.cur, param, nameOf(trait), slot, pos);
        k: str = "";
        k = keepString(key);
        if (self.depKeys.has(k)) { return; }
        self.depKeys.put(k, true);
        self.deps.push(DepFact { param: param, trait: trait, slot: slot, pos: pos });
        self.depNext.push(self.depHead.get(self.cur));
        self.depHead.set(self.cur, self.deps.len() - 1);
        self.changed = true;
    }

    // Parameter `r` of the function being scanned reaches position `pos` of call `c`: whatever
    // dispatches the callee hands that position to, this function hands `r` to.
    inheritDeps &self inout a:Ast c:CallNode pos:long r:long -> void {
        if (c.slot == SLOT_FNPTR || c.callee != NO_NODE) { return; }
        if (c.slot != NO_SLOT) {
            self.addDep(r, a.expr(c.receiver).structName, c.slot, pos);
            return;
        }
        hit: Option<long> = self.fnAt.find(nameOf(c.name));
        g: long = -1;
        match hit { Some(i) { g = i; } None { return; } }
        if (isExternFn(g)) {
            fi: long = fnFactOf(g);
            if (fi < 0) { return; }
            fact: FnFact = gFacts.fns.get(fi);
            for k in 0..fact.depCount {
                d: DepFact = gFacts.depAt(fact, k);
                if (d.param == pos) { self.addDep(r, d.trait, d.slot, d.pos); }
            }
            return;
        }
        d: long = self.depHead.get(g);
        while (d >= 0) {
            dd: DepFact = self.deps.get(d);
            if (dd.param == pos) { self.addDep(r, dd.trait, dd.slot, dd.pos); }
            d = self.depNext.get(d);
        }
    }

    // ─── which parameters a function writes through ──────────────────────────

    scanFunction &self inout a:Ast at:long -> void {
        if (isUnchecked(at) && !isExternFn(at)) { return; }
        // A dependency's function: its own compile's mask, and its dispatches asked again of
        // the implementations this program has.
        if (isExternFn(at)) {
            fi: long = fnFactOf(at);
            if (fi < 0) { return; }
            fact: FnFact = gFacts.fns.get(fi);
            m: long = self.writes.get(at);
            k: long = 0;
            while (k < fact.depCount && m != WRITES_ALL) {
                d: DepFact = gFacts.depAt(fact, k);
                if (self.dispatchWritesTrait(a, d.trait, d.slot, d.pos)) { m = m | (1 << d.param); }
                k = k + 1;
            }
            if (m != self.writes.get(at)) { self.writes.set(at, m); self.changed = true; }
            return;
        }
        self.cur = at;
        f: FnNode = a.fns.get(at);
        self.paramIx.clear();
        self.alias.clear();
        for k in 0..f.argCount {
            p: VarDeclNode = a.paramAt(f, k);
            if (throughParam(p)) { self.paramIx.put(nameOf(p.name), k); }
        }
        self.mask = self.writes.get(at);
        if (!self.paramIx.isEmpty() && self.mask != WRITES_ALL) { self.scanBlock(a, f.body); }
        if (self.mask != self.writes.get(at)) { self.writes.set(at, self.mask); self.changed = true; }
    }

    scanBlock &self inout a:Ast b:long -> void {
        if (b < 0) { return; }
        n: long = a.blockLen(b);
        for k in 0..n { self.scanStmt(a, a.stmtAt(b, k)); }
    }

    scanStmt &self inout a:Ast st:Stmt -> void {
        if (st.kind == StmtKind.VarDecl) {
            d: VarDeclNode = a.decls.get(st.at);
            self.forgetAlias(d.name);
            self.scanExpr(a, d.init);
            return;
        }
        if (st.kind == StmtKind.Expr || st.kind == StmtKind.Call) { self.scanExpr(a, a.exprStmts.get(st.at).value); return; }
        if (st.kind == StmtKind.Return) { self.scanExpr(a, a.returns.get(st.at).value); return; }
        if (st.kind == StmtKind.If) {
            at: long = st.at;
            while (at >= 0) {
                br: IfNode = a.ifs.get(at);
                self.scanExpr(a, br.cond);
                self.scanBlock(a, br.body);
                at = br.elseIf;
            }
            return;
        }
        if (st.kind == StmtKind.While) {
            w: WhileNode = a.whiles.get(st.at);
            self.scanExpr(a, w.cond); self.scanBlock(a, w.body); self.scanBlock(a, w.step);
            return;
        }
        if (st.kind == StmtKind.Loop || st.kind == StmtKind.Block || st.kind == StmtKind.Unsafe) {
            self.scanBlock(a, a.blockStmts.get(st.at).body);
            return;
        }
        if (st.kind == StmtKind.Match) {
            m: MatchNode = a.matches.get(st.at);
            for k in 0..m.armCount { self.scanBlock(a, a.arms.get(m.firstArm + k).body); }
            return;
        }
        if (st.kind == StmtKind.With) {
            w: WithNode = a.withs.get(st.at);
            self.markParam(w.name);
            self.scanBlock(a, a.withs.get(st.at).body);
            return;
        }
        if (st.kind == StmtKind.Destructure) { self.scanExpr(a, a.destructures.get(st.at).value); return; }
        if (st.kind == StmtKind.Asm) {
            n: AsmNode = a.asms.get(st.at);
            for k in 0..n.pieceCount {
                pc: AsmPiece = a.asmPieces.get(n.firstPiece + k);
                if (pc.kind == AsmKind.In) {
                    self.scanExpr(a, pc.value);
                    r: long = self.rootParam(a, pc.value);
                    if (r >= 0) { self.mask = self.mask | (1 << r); }
                }
                if (pc.kind == AsmKind.Out) { self.markParam(pc.name); }
            }
            return;
        }
    }

    markParam &self n:Sym -> void {
        hit: Option<long> = self.paramIx.find(nameOf(n));
        match hit { Some(i) { self.mask = self.mask | (1 << i); } None { } }
    }

    scanExpr &self inout a:Ast id:NodeId -> void {
        if (id == NO_NODE) { return; }
        e: Expr = a.expr(id);
        if (e.op == Op.Assignment && self.noteAlias(a, e)) { return; }
        if (e.op == Op.Assignment) {
            if (throughPointer(a, e.left)) { self.mask = WRITES_ALL; }
            r: long = self.rootParam(a, e.left);
            if (r >= 0) { self.mask = self.mask | (1 << r); }
            self.scanExpr(a, e.left);
            self.scanExpr(a, e.right);
            return;
        }
        if (e.left != NO_NODE) { self.scanExpr(a, e.left); self.scanExpr(a, e.right); return; }
        if (e.op == Op.AddressOf) {
            match e.payload {
                Sub(v) {
                    if (e.kind != Lit.Fn) { r: long = self.rootParam(a, v); if (r >= 0) { self.mask = self.mask | (1 << r); } }
                    self.scanExpr(a, v);
                }
                _ { }
            }
            return;
        }
        if (e.op == Op.FunctionCall || e.op == Op.MethodCall) {
            c: CallNode = a.calls.get(0);
            match e.payload { Call(i) { c = a.calls.get(i); } _ { } }
            nodes: Vec<NodeId>;
            if (c.receiver != NO_NODE) { nodes.push(c.receiver); }
            for k in 0..c.argCount { nodes.push(a.argAt(c, k)); }
            for k in 0..nodes.len() { self.scanExpr(a, nodes.get(k)); }
            for k in 0..nodes.len() {
                r: long = -1;
                if (!strWord(a, nodes.get(k))) { r = self.rootParam(a, nodes.get(k)); }
                if (r >= 0 && self.calleeWrites(a, c, k)) { self.mask = self.mask | (1 << r); }
                if (r >= 0 && gKlibMode) { self.inheritDeps(a, c, k, r); }
            }
            return;
        }
        match e.payload {
            Sub(v)   { self.scanExpr(a, v); }
            Field(i) { self.scanExpr(a, a.fields.get(i).base); }
            Index(i) {
                ix: IndexNode = a.indexes.get(i);
                self.scanExpr(a, ix.base); self.scanExpr(a, ix.index);
                self.scanExpr(a, ix.sliceStart); self.scanExpr(a, ix.sliceEnd);
            }
            Lit(i) {
                l: LitNode = a.lits.get(i);
                for k in 0..l.initCount { self.scanExpr(a, a.inits.get(l.firstInit + k).value); }
                self.scanExpr(a, l.rest);
            }
            _ { }
        }
    }

    // ─── where a function writes a parameter, field by field (on demand) ────

    // Where the callee of `c` writes its parameter at position `pos`, as paths below it; [""]
    // when it is not known field by field (a dispatch, a fn value, a dependency's function).
    calleePaths &self inout a:Ast c:CallNode pos:long -> Vec<Sym> {
        out: Vec<Sym>;
        whole: Sym = intern("");
        if (c.slot != NO_SLOT || c.callee != NO_NODE) { out.push(whole); return out; }
        i: long = self.calleeAt(a, c);
        if (i < 0) { out.push(whole); return out; }
        at: long = self.paramPos(a, i, pos);
        if (at < 0 || isExternFn(i) || isUnchecked(i) || self.writes.get(i) == WRITES_ALL) { out.push(whole); return out; }
        self.pathsOf(a, i, at);
        return self.knownPaths(i, at);
    }

    calleeAt &self inout a:Ast c:CallNode -> long {
        hit: Option<long> = self.fnAt.find(nameOf(c.name));
        match hit { Some(x) { return x; } None { } }
        return -1;
    }

    // The parameter argument `pos` of a call to function `i` lands in (a variadic run's is the last).
    paramPos &self inout a:Ast i:long pos:long -> long {
        f: FnNode = a.fns.get(i);
        if (pos >= f.argCount && f.argCount > 0 && a.paramAt(f, f.argCount - 1).isVariadic) { return f.argCount - 1; }
        if (pos >= f.argCount || pos >= 62) { return -1; }
        return pos;
    }

    knownPaths &self i:long at:long -> Vec<Sym> {
        out: Vec<Sym>;
        d: long = self.wpHead.get(i);
        while (d >= 0) {
            if (self.wpParam.get(d) == at) { out.push(self.wpPath.get(d)); }
            d = self.wpNext.get(d);
        }
        return out;
    }

    // Work out where function `i` writes parameter `at`, and everything that answer waits on: a
    // walk that meets a callee whose answer is not known yet stops, the callee is worked out
    // first, and the walk is made again.
    pathsOf &self inout a:Ast i:long at:long -> void {
        if ((self.wpDone.get(i) & (1 << at)) != 0) { return; }
        self.wpStackF.push(i);
        self.wpStackP.push(at);
        self.wpBusy.set(i, self.wpBusy.get(i) | (1 << at));
        while (self.wpStackF.len() > 0) {
            f: long = self.wpStackF.last();
            p: long = self.wpStackP.last();
            self.wpNeedF = -1;
            self.wpWalk(a, f, p);
            if (self.wpNeedF >= 0) {
                self.wpStackF.push(self.wpNeedF);
                self.wpStackP.push(self.wpNeedP);
                self.wpBusy.set(self.wpNeedF, self.wpBusy.get(self.wpNeedF) | (1 << self.wpNeedP));
                continue;
            }
            for q in self.wpOut {
                self.wpParam.push(p);
                self.wpPath.push(q);
                self.wpNext.push(self.wpHead.get(f));
                self.wpHead.set(f, self.wpParam.len() - 1);
            }
            self.wpDone.set(f, self.wpDone.get(f) | (1 << p));
            self.wpBusy.set(f, self.wpBusy.get(f) & ~(1 << p));
            self.wpStackF.pop();
            self.wpStackP.pop();
        }
    }

    // One walk of function `f`'s body for where it writes parameter `p`, into `wpOut`.
    wpWalk &self inout a:Ast f:long p:long -> void {
        self.wpOut.clear();
        self.wpIx.clear();
        self.wpAlias.clear();
        self.wpTarget = p;
        fn: FnNode = a.fns.get(f);
        if (self.writes.get(f) == WRITES_ALL || isExternFn(f) || isUnchecked(f)) { self.wpAdd(intern("")); return; }
        if ((self.writes.get(f) & (1 << p)) == 0) { return; }
        for k in 0..fn.argCount {
            pd: VarDeclNode = a.paramAt(fn, k);
            if (throughParam(pd)) { self.wpIx.put(nameOf(pd.name), k); }
        }
        self.wpBlock(a, fn.body);
    }

    wpAdd &self q:Sym -> void {
        for x in self.wpOut { if (x == q || nameOf(x).len == 0) { return; } }
        if (nameOf(q).len == 0) { self.wpOut.clear(); }
        self.wpOut.push(q);
    }

    wpBlock &self inout a:Ast b:long -> void {
        if (b < 0) { return; }
        for k in 0..a.blockLen(b) {
            if (self.wpNeedF >= 0) { return; }
            self.wpStmt(a, a.stmtAt(b, k));
        }
    }

    wpStmt &self inout a:Ast st:Stmt -> void {
        if (st.kind == StmtKind.VarDecl) {
            d: VarDeclNode = a.decls.get(st.at);
            if (self.wpAlias.len() > 0) { self.wpAlias.remove(nameOf(d.name)); }
            self.wpExpr(a, d.init);
            return;
        }
        if (st.kind == StmtKind.Expr || st.kind == StmtKind.Call) { self.wpExpr(a, a.exprStmts.get(st.at).value); return; }
        if (st.kind == StmtKind.Return) { self.wpExpr(a, a.returns.get(st.at).value); return; }
        if (st.kind == StmtKind.If) {
            at: long = st.at;
            while (at >= 0) {
                br: IfNode = a.ifs.get(at);
                self.wpExpr(a, br.cond);
                self.wpBlock(a, br.body);
                at = br.elseIf;
            }
            return;
        }
        if (st.kind == StmtKind.While) {
            w: WhileNode = a.whiles.get(st.at);
            self.wpExpr(a, w.cond); self.wpBlock(a, w.body); self.wpBlock(a, w.step);
            return;
        }
        if (st.kind == StmtKind.Loop || st.kind == StmtKind.Block || st.kind == StmtKind.Unsafe) {
            self.wpBlock(a, a.blockStmts.get(st.at).body);
            return;
        }
        if (st.kind == StmtKind.Match) {
            m: MatchNode = a.matches.get(st.at);
            for k in 0..m.armCount { self.wpBlock(a, a.arms.get(m.firstArm + k).body); }
            return;
        }
        if (st.kind == StmtKind.With) {
            w: WithNode = a.withs.get(st.at);
            if (self.wpIs(w.name)) { self.wpAdd(intern("")); }
            self.wpBlock(a, w.body);
            return;
        }
        if (st.kind == StmtKind.Destructure) { self.wpExpr(a, a.destructures.get(st.at).value); return; }
        if (st.kind == StmtKind.Asm) {
            n: AsmNode = a.asms.get(st.at);
            for k in 0..n.pieceCount {
                pc: AsmPiece = a.asmPieces.get(n.firstPiece + k);
                if (pc.kind == AsmKind.In) {
                    self.wpExpr(a, pc.value);
                    path: String;
                    if (self.paramPlaceOf(a, pc.value, &path) == self.wpTarget) { self.wpAdd(intern("")); }
                }
                if (pc.kind == AsmKind.Out && self.wpIs(pc.name)) { self.wpAdd(intern("")); }
            }
        }
    }

    // Is `n` the parameter the walk is for?
    wpIs &self n:Sym -> bool {
        hit: Option<long> = self.wpIx.find(nameOf(n));
        match hit { Some(i) { return i == self.wpTarget; } None { } }
        return false;
    }

    wpExpr &self inout a:Ast id:NodeId -> void {
        if (id == NO_NODE || self.wpNeedF >= 0) { return; }
        e: Expr = a.expr(id);
        if (e.op == Op.Assignment) {
            // `r = &place` into a borrow local: a second name for the place, not a write of it.
            l: Expr = a.expr(e.left);
            r: Expr = a.expr(e.right);
            if (l.op == Op.Lvalue && l.kind == Lit.Ref && r.op == Op.AddressOf && r.kind != Lit.Fn) {
                n: Sym = NO_SYM;
                match l.payload { Name(x) { n = x; } _ { } }
                match r.payload { Sub(v) { if (n != NO_SYM) { self.wpAlias.put(nameOf(n), v); return; } } _ { } }
            }
            path: String;
            if (self.paramPlaceOf(a, e.left, &path) == self.wpTarget) { self.wpAdd(internString(path)); }
            self.wpExpr(a, e.left);
            self.wpExpr(a, e.right);
            return;
        }
        if (e.left != NO_NODE) { self.wpExpr(a, e.left); self.wpExpr(a, e.right); return; }
        if (e.op == Op.AddressOf) {
            match e.payload {
                Sub(v) {
                    path: String;
                    if (e.kind != Lit.Fn && self.paramPlaceOf(a, v, &path) == self.wpTarget) { self.wpAdd(intern("")); }
                    self.wpExpr(a, v);
                }
                _ { }
            }
            return;
        }
        if (e.op == Op.FunctionCall || e.op == Op.MethodCall) {
            c: CallNode = a.calls.get(0);
            match e.payload { Call(i) { c = a.calls.get(i); } _ { } }
            nodes: Vec<NodeId>;
            if (c.receiver != NO_NODE) { nodes.push(c.receiver); }
            for k in 0..c.argCount { nodes.push(a.argAt(c, k)); }
            for k in 0..nodes.len() {
                // `&self.seen` lent to a function's parameter: what that function writes through it
                // is what is written (below), not all of what `self` is.
                nd: Expr = a.expr(nodes.get(k));
                lent: NodeId = NO_NODE;
                if (nd.op == Op.AddressOf && nd.kind != Lit.Fn && self.lendsTo(a, c, k)) {
                    match nd.payload { Sub(v) { lent = v; } _ { } }
                }
                if (lent != NO_NODE) { self.wpExpr(a, lent); } else { self.wpExpr(a, nodes.get(k)); }
                if (self.wpNeedF >= 0) { return; }
            }
            for k in 0..nodes.len() {
                if (strWord(a, nodes.get(k))) { continue; }
                path: String;
                if (self.paramPlaceOf(a, nodes.get(k), &path) != self.wpTarget) { continue; }
                if (!self.calleeWrites(a, c, k)) { continue; }
                cut: bool = self.ppCut;
                room: long = WP_DEPTH - self.ppDepth;
                qs: Vec<Sym> = self.wpCallee(a, c, k);
                if (self.wpNeedF >= 0) { return; }
                for q in qs {
                    if (cut || room <= 0 || nameOf(q).len == 0) { self.wpAdd(internString(path)); continue; }
                    whole: String;
                    whole.pushString(path);
                    pushFields(&whole, nameOf(q), room);
                    self.wpAdd(internString(whole));
                }
            }
            return;
        }
        match e.payload {
            Sub(v)   { self.wpExpr(a, v); }
            Field(i) { self.wpExpr(a, a.fields.get(i).base); }
            Index(i) {
                ix: IndexNode = a.indexes.get(i);
                self.wpExpr(a, ix.base); self.wpExpr(a, ix.index);
                self.wpExpr(a, ix.sliceStart); self.wpExpr(a, ix.sliceEnd);
            }
            Lit(i) {
                l: LitNode = a.lits.get(i);
                for k in 0..l.initCount { self.wpExpr(a, a.inits.get(l.firstInit + k).value); }
                self.wpExpr(a, l.rest);
            }
            _ { }
        }
    }

    // A callee's paths inside a walk: known, "all of it" when it cannot be said field by field or
    // is being worked out already, and otherwise the walk stops for it (`wpNeedF`).
    wpCallee &self inout a:Ast c:CallNode pos:long -> Vec<Sym> {
        out: Vec<Sym>;
        whole: Sym = intern("");
        if (c.slot != NO_SLOT || c.callee != NO_NODE) { out.push(whole); return out; }
        i: long = self.calleeAt(a, c);
        if (i < 0) { out.push(whole); return out; }
        at: long = self.paramPos(a, i, pos);
        if (at < 0 || isExternFn(i) || isUnchecked(i) || self.writes.get(i) == WRITES_ALL) { out.push(whole); return out; }
        if ((self.wpDone.get(i) & (1 << at)) != 0) { return self.knownPaths(i, at); }
        if ((self.wpBusy.get(i) & (1 << at)) != 0) { out.push(whole); return out; }
        self.wpNeedF = i;
        self.wpNeedP = at;
        return out;
    }

    // Is position `pos` of call `c` a known function's borrowing parameter (not a raw pointer)?
    lendsTo &self inout a:Ast c:CallNode pos:long -> bool {
        if (c.slot != NO_SLOT || c.callee != NO_NODE) { return false; }
        i: long = self.calleeAt(a, c);
        if (i < 0) { return false; }
        f: FnNode = a.fns.get(i);
        if (pos >= f.argCount) { return false; }
        p: VarDeclNode = a.paramAt(f, pos);
        return throughParam(p) && p.kind != Lit.Ptr;
    }

    // `paramPlace` from a fresh start.
    paramPlaceOf &self inout a:Ast id:NodeId inout path:String -> long {
        self.ppCut = false;
        self.ppDepth = 0;
        return self.paramPlace(a, id, path);
    }

    // The parameter `id` is rooted at (as `rootParam` finds it, over the walk's own tables) and,
    // into `path`, the fields below it the place names, cut (`ppCut`) at the first step that is
    // not a field or at WP_DEPTH.
    paramPlace &self inout a:Ast id:NodeId inout path:String -> long {
        if (id == NO_NODE) { return -1; }
        e: Expr = a.expr(id);
        if (e.op == Op.Lvalue) {
            match e.payload {
                Name(n) {
                    hit: Option<long> = self.wpIx.find(nameOf(n));
                    match hit { Some(i) { return i; } None { } }
                    if (self.wpAlias.len() > 0) {
                        src: Option<NodeId> = self.wpAlias.find(nameOf(n));
                        match src { Some(s) { return self.paramPlace(a, s, path); } None { } }
                    }
                }
                _ { }
            }
            return -1;
        }
        if (e.op == Op.FunctionCall || e.op == Op.MethodCall) {
            if (e.kind != Lit.Ref && e.kind != Lit.Ptr && e.kind != Lit.Slice) { return -1; }
            c: CallNode = a.calls.get(0);
            match e.payload { Call(i) { c = a.calls.get(i); } _ { } }
            r: long = self.paramPlace(a, c.receiver, path);
            if (r >= 0) { self.ppCut = true; return r; }
            for k in 0..c.argCount {
                path.clear();
                self.ppDepth = 0;
                r = self.paramPlace(a, a.argAt(c, k), path);
                if (r >= 0) { self.ppCut = true; return r; }
            }
            path.clear();
            self.ppDepth = 0;
            return -1;
        }
        match e.payload {
            Sub(v) {
                r: long = self.paramPlace(a, v, path);
                // `&place` names the place; `*p` of a lent parameter is that parameter's place; any
                // other dereference or cast reaches past what a field path can say.
                if (r >= 0 && e.op != Op.AddressOf && !(e.op == Op.Deref && lentPlaceOf(a, id) != NO_NODE)) { self.ppCut = true; }
                return r;
            }
            Field(i) {
                r: long = self.paramPlace(a, a.fields.get(i).base, path);
                if (r < 0 || self.ppCut) { return r; }
                if (self.ppDepth >= WP_DEPTH) { self.ppCut = true; return r; }
                if (path.len > 0) { path.push('.'); }
                path.pushStr(nameOf(a.fields.get(i).name));
                self.ppDepth = self.ppDepth + 1;
                return r;
            }
            Index(i) {
                ix: IndexNode = a.indexes.get(i);
                r: long = -1;
                if (ix.base != NO_NODE) { r = self.paramPlace(a, ix.base, path); }
                else {
                    ih: Option<long> = self.wpIx.find(nameOf(ix.name));
                    match ih { Some(k) { r = k; } None { } }
                }
                if (r >= 0) { self.ppCut = true; }
                return r;
            }
            _ { }
        }
        return -1;
    }

    // Whether the callee of `c` writes through its parameter at position `pos` (the receiver
    // is position 0). Unknown callees -- a function value, a dispatch some implementation of
    // which writes -- answer yes.
    calleeWrites &self inout a:Ast c:CallNode pos:long -> bool {
        if (c.slot == SLOT_FNPTR || c.callee != NO_NODE) { return !fnValueArgPlain(a, c, pos); }
        if (c.slot != NO_SLOT) { return self.dispatchWrites(a, c, pos); }
        hit: Option<long> = self.fnAt.find(nameOf(c.name));
        match hit {
            Some(i) {
                f: FnNode = a.fns.get(i);
                // Every argument of a variadic run is the one parameter that takes the run: the
                // third argument to `eprintln` is its `rest`, not a parameter past its last.
                at: long = pos;
                if (at >= f.argCount && f.argCount > 0 && a.paramAt(f, f.argCount - 1).isVariadic) {
                    at = f.argCount - 1;
                }
                if (at >= f.argCount) { return true; }
                if (!throughParam(a.paramAt(f, at))) { return false; }   // a copy: the caller's is untouched
                w: long = self.writes.get(i);
                return w == WRITES_ALL || (w & (1 << at)) != 0;
            }
            None { }
        }
        return true;    // no body to read: a syscall, or external
    }
    // A dispatch reaches whichever implementation the object holds: every registered one of the
    // trait is possible, so the slot writes if any of them does.
    dispatchWrites &self inout a:Ast c:CallNode pos:long -> bool {
        recv: Expr = a.expr(c.receiver);
        return self.dispatchWritesTrait(a, recv.structName, c.slot, pos);
    }
    // The same for a dispatch named by its trait and slot rather than by a call in front of us.
    dispatchWritesTrait &self inout a:Ast trait:Sym slot:long pos:long -> bool {
        for i in 0..gReg.implCount() {
            im: TraitImplDef = gReg.implAt(i);
            if (intern(gReg.traitMangled(im.trait)) == trait) {
                ti: long = gReg.findTrait(nameOf(im.trait.name));
                if (ti >= 0) {
                    t: TraitDef = gReg.traitDef(ti);
                    if (slot >= 0 && slot < t.methodCount) {
                        m: Sym = implMethodName(im, gReg.traitMethodAt(t, slot).name);
                        hit: Option<long> = self.fnAt.find(nameOf(m));
                        match hit {
                            Some(fi) {
                                f: FnNode = a.fns.get(fi);
                                if (pos < f.argCount && throughParam(a.paramAt(f, pos))) {
                                    w: long = self.writes.get(fi);
                                    if (w == WRITES_ALL || (w & (1 << pos)) != 0) { return true; }
                                }
                            }
                            None { return true; }
                        }
                    }
                }
            }
        }
        return false;
    }

    // A declaration begins a new variable, so whatever an earlier one of that name was bound to
    // no longer stands for it. Locals are renamed only where one shadows another, so two sibling
    // scopes may each declare a `v` (two `match` arms), and the second's `v = eval(...)` is no
    // write through the first's borrow of a parameter. Every walk that notes borrow locals reads
    // a body in order and forgets a name at its declaration.
    forgetAlias &self n:Sym -> void {
        if (self.alias.len() > 0) { self.alias.remove(nameOf(n)); }
    }

    // `r = &place` into a borrow local: not a write of the place, only a second name for it, and
    // what is written through that name is written to the place. True when it was one.
    noteAlias &self inout a:Ast e:Expr -> bool {
        l: Expr = a.expr(e.left);
        if (l.op != Op.Lvalue || l.kind != Lit.Ref) { return false; }
        r: Expr = a.expr(e.right);
        if (r.op != Op.AddressOf || r.kind == Lit.Fn) { return false; }
        n: Sym = NO_SYM;
        match l.payload { Name(x) { n = x; } _ { } }
        if (n == NO_SYM) { return false; }
        match r.payload {
            Sub(v) { self.alias.put(nameOf(n), v); return true; }
            _ { }
        }
        return false;
    }

    // The parameter an expression is rooted at, or -1: a local's name, through fields, elements,
    // dereferences, casts and borrows; a call yielding a borrow or a pointer is rooted wherever
    // its receiver or any argument is.
    rootParam &self inout a:Ast id:NodeId -> long {
        if (id == NO_NODE) { return -1; }
        e: Expr = a.expr(id);
        if (e.op == Op.Lvalue) {
            match e.payload {
                Name(n) {
                    hit: Option<long> = self.paramIx.find(nameOf(n));
                    match hit { Some(i) { return i; } None { } }
                    if (self.alias.len() > 0) {
                        src: Option<NodeId> = self.alias.find(nameOf(n));
                        match src { Some(s) { return self.rootParam(a, s); } None { } }
                    }
                }
                _ { }
            }
            return -1;
        }
        if (e.op == Op.FunctionCall || e.op == Op.MethodCall) {
            if (e.kind != Lit.Ref && e.kind != Lit.Ptr && e.kind != Lit.Slice) { return -1; }
            c: CallNode = a.calls.get(0);
            match e.payload { Call(i) { c = a.calls.get(i); } _ { } }
            r: long = self.rootParam(a, c.receiver);
            if (r >= 0) { return r; }
            for k in 0..c.argCount { r = self.rootParam(a, a.argAt(c, k)); if (r >= 0) { return r; } }
            return -1;
        }
        match e.payload {
            Sub(v)   { return self.rootParam(a, v); }
            Field(i) { return self.rootParam(a, a.fields.get(i).base); }
            Index(i) {
                ix: IndexNode = a.indexes.get(i);
                if (ix.base != NO_NODE) { return self.rootParam(a, ix.base); }
                ih: Option<long> = self.paramIx.find(nameOf(ix.name));
                match ih { Some(k) { return k; } None { } }
            }
            _ { }
        }
        return -1;
    }

    // ─── holding every use of a const to it ─────────────────────────────────

    guardBlock &self inout a:Ast b:long -> void {
        if (b < 0) { return; }
        n: long = a.blockLen(b);
        for k in 0..n {
            w: long = a.enterStmt(a.stmtIdAt(b, k));
            self.guardStmt(a, a.stmtAt(b, k));
            gPos = w;
        }
    }

    guardStmt &self inout a:Ast st:Stmt -> void {
        if (st.kind == StmtKind.VarDecl) {
            d: VarDeclNode = a.decls.get(st.at);
            self.forgetAlias(d.name);
            self.guardExpr(a, d.init);
            return;
        }
        if (st.kind == StmtKind.Expr || st.kind == StmtKind.Call) { self.guardExpr(a, a.exprStmts.get(st.at).value); return; }
        if (st.kind == StmtKind.Return) { self.guardExpr(a, a.returns.get(st.at).value); return; }
        if (st.kind == StmtKind.If) {
            at: long = st.at;
            while (at >= 0) {
                br: IfNode = a.ifs.get(at);
                self.guardExpr(a, br.cond);
                self.guardBlock(a, br.body);
                at = br.elseIf;
            }
            return;
        }
        if (st.kind == StmtKind.While) {
            w: WhileNode = a.whiles.get(st.at);
            self.guardExpr(a, w.cond); self.guardBlock(a, w.body); self.guardBlock(a, w.step);
            return;
        }
        if (st.kind == StmtKind.Loop || st.kind == StmtKind.Block || st.kind == StmtKind.Unsafe) {
            self.guardBlock(a, a.blockStmts.get(st.at).body);
            return;
        }
        if (st.kind == StmtKind.Match) {
            m: MatchNode = a.matches.get(st.at);
            for k in 0..m.armCount { self.guardBlock(a, a.arms.get(m.firstArm + k).body); }
            return;
        }
        if (st.kind == StmtKind.With) {
            w: WithNode = a.withs.get(st.at);
            if (isImmutableGlobal(w.name)) { refuse(w.name, "is held by `with`, which writes it"); }
            self.guardBlock(a, w.body);
            return;
        }
        if (st.kind == StmtKind.Destructure) { self.guardExpr(a, a.destructures.get(st.at).value); return; }
        if (st.kind == StmtKind.Asm) {
            n: AsmNode = a.asms.get(st.at);
            for k in 0..n.pieceCount {
                pc: AsmPiece = a.asmPieces.get(n.firstPiece + k);
                if (pc.kind == AsmKind.In) {
                    self.guardExpr(a, pc.value);
                    c: Sym = self.rootConst(a, pc.value);
                    if (c != NO_SYM) { refuse(c, "is handed to an `asm` block, which may write it"); }
                }
                if (pc.kind == AsmKind.Out && isImmutableGlobal(pc.name)) { refuse(pc.name, "is written by an `asm` block's `out`"); }
            }
            return;
        }
    }

    guardExpr &self inout a:Ast id:NodeId -> void {
        if (id == NO_NODE) { return; }
        e: Expr = a.expr(id);
        if (e.op == Op.Assignment && self.noteAlias(a, e)) { return; }
        if (e.op == Op.Assignment) {
            c: Sym = self.rootConst(a, e.left);
            if (c != NO_SYM) { refuse(c, "is assigned to"); }
            self.guardExpr(a, e.left);
            self.guardExpr(a, e.right);
            return;
        }
        if (e.left != NO_NODE) { self.guardExpr(a, e.left); self.guardExpr(a, e.right); return; }
        if (e.op == Op.AddressOf) {
            match e.payload {
                Sub(v) {
                    if (e.kind != Lit.Fn) {
                        c: Sym = self.rootConst(a, v);
                        if (c != NO_SYM) { refuse(c, "is lent with `&`, which allows writing it"); }
                    }
                    self.guardExpr(a, v);
                }
                _ { }
            }
            return;
        }
        if (e.op == Op.FunctionCall || e.op == Op.MethodCall) {
            c: CallNode = a.calls.get(0);
            match e.payload { Call(i) { c = a.calls.get(i); } _ { } }
            nodes: Vec<NodeId>;
            if (c.receiver != NO_NODE) { nodes.push(c.receiver); }
            for k in 0..c.argCount { nodes.push(a.argAt(c, k)); }
            for k in 0..nodes.len() {
                self.guardExpr(a, nodes.get(k));
                g: Sym = NO_SYM;
                if (!strWord(a, nodes.get(k))) { g = self.rootConst(a, nodes.get(k)); }
                if (g != NO_SYM) { self.guardArgument(a, c, k, g); }
            }
            return;
        }
        match e.payload {
            Sub(v)   { self.guardExpr(a, v); }
            Field(i) { self.guardExpr(a, a.fields.get(i).base); }
            Index(i) {
                ix: IndexNode = a.indexes.get(i);
                self.guardExpr(a, ix.base); self.guardExpr(a, ix.index);
                self.guardExpr(a, ix.sliceStart); self.guardExpr(a, ix.sliceEnd);
            }
            Lit(i) {
                l: LitNode = a.lits.get(i);
                for k in 0..l.initCount { self.guardExpr(a, a.inits.get(l.firstInit + k).value); }
                self.guardExpr(a, l.rest);
            }
            _ { }
        }
    }

    // A const, or part of one, as the argument at `pos` of a call: fine for a parameter the
    // callee only reads, and for a copy; refused for one it writes through, and for a move.
    guardArgument &self inout a:Ast c:CallNode pos:long g:Sym -> void {
        if (c.slot == SLOT_FNPTR || c.callee != NO_NODE) {
            // The callee is unknown, but what crosses can say enough: a scalar or a `str` arrives
            // as a copy of the value or of the view (a str's bytes are never written through
            // it), so no callee can write the const through it. The fn type's parameter is asked
            // when it has one, the argument's own type otherwise. Anything else (a struct, a
            // slice) stays refused: which function the value holds is not known here.
            if (fnValueArgPlain(a, c, pos)) { return; }
            refuse(g, "is passed through a function value, whose callee cannot be checked");
        }
        if (c.slot != NO_SLOT) {
            if (self.dispatchWrites(a, c, pos)) { refuseStr(g, format("is dispatched to '{}', which some implementation writes", nameOf(c.name))); }
            return;
        }
        hit: Option<long> = self.fnAt.find(nameOf(c.name));
        match hit {
            Some(i) {
                f: FnNode = a.fns.get(i);
                if (pos >= f.argCount) { return; }
                p: VarDeclNode = a.paramAt(f, pos);
                if (throughParam(p)) {
                    w: long = self.writes.get(i);
                    if (w == WRITES_ALL || (w & (1 << pos)) != 0) {
                        refuseStr(g, format("is handed to '{}', which writes its parameter '{}'", nameOf(c.name), nameOf(p.name)));
                    }
                    return;
                }
                if (p.kind == Lit.Struct && p.conv == Conv.Sink && gReg.needsDrop(p.structName)) {
                    refuseStr(g, format("would be moved out of, into '{}'", nameOf(c.name)));
                }
            }
            None { refuseStr(g, format("is handed to '{}', whose body the compiler does not hold", nameOf(c.name))); }
        }
    }

    // The const global an expression is rooted at, or NO_SYM. Same shape as `rootParam`.
    rootConst &self inout a:Ast id:NodeId -> Sym {
        if (id == NO_NODE) { return NO_SYM; }
        e: Expr = a.expr(id);
        if (e.op == Op.Lvalue) {
            match e.payload {
                Name(n) {
                    if (isImmutableGlobal(n)) { return n; }
                    if (self.alias.len() > 0) {
                        src: Option<NodeId> = self.alias.find(nameOf(n));
                        match src { Some(s) { return self.rootConst(a, s); } None { } }
                    }
                }
                _ { }
            }
            return NO_SYM;
        }
        if (e.op == Op.FunctionCall || e.op == Op.MethodCall) {
            if (e.kind != Lit.Ref && e.kind != Lit.Ptr && e.kind != Lit.Slice) { return NO_SYM; }
            c: CallNode = a.calls.get(0);
            match e.payload { Call(i) { c = a.calls.get(i); } _ { } }
            r: Sym = self.rootConst(a, c.receiver);
            if (r != NO_SYM) { return r; }
            for k in 0..c.argCount { r = self.rootConst(a, a.argAt(c, k)); if (r != NO_SYM) { return r; } }
            return NO_SYM;
        }
        match e.payload {
            Sub(v)   { return self.rootConst(a, v); }
            Field(i) { return self.rootConst(a, a.fields.get(i).base); }
            Index(i) {
                ix: IndexNode = a.indexes.get(i);
                if (ix.base != NO_NODE) { return self.rootConst(a, ix.base); }
                if (isImmutableGlobal(ix.name)) { return ix.name; }
            }
            _ { }
        }
        return NO_SYM;
    }

    // ─── what a `for x in xs` holds ──────────────────────────────────────────
    //
    // The loop read `xs`'s buffer and length once, and `x` may be a borrow into the buffer
    // (`Checker.bmForLoop`), so while the body runs `xs` stays as it is: the body may read it,
    // and may not assign to it, lend it with `&`, hand it to a callee that writes through that
    // parameter or takes it, or move it. Writing an element through `x` is what `for x in &xs`
    // is for; in the plain form a struct element is read-only, as a `read` parameter is, and a
    // scalar is the loop's own copy. It is the rule a match arm holding a borrow lives by
    // (`Checker.bmArmBlock`), held here because only here is it known which callees write
    // through which parameters: `xs.len()` reads, `xs.push(v)` writes. Like that rule it reads
    // the places the body names; a callee that reaches the collection another way (a `var`
    // global it writes by name) is not seen.

    holdFunction &self inout a:Ast at:long -> void {
        self.hFn = at;
        body: long = a.fns.get(at).body;
        self.alias.clear();
        self.holdScan(a, body);
        self.alias.clear();
    }

    // A borrow local's place and a loop pointer's setup (`$forpK = xs.buf.ptr`), noted as the
    // body is read in order; a declaration forgets what an earlier local of its name was bound
    // to (`forgetAlias`: two sibling scopes may each declare one).
    holdNote &self inout a:Ast st:Stmt -> void {
        if (st.kind == StmtKind.VarDecl) { self.forgetAlias(a.decls.get(st.at).name); return; }
        if (st.kind != StmtKind.Expr) { return; }
        e: Expr = a.expr(a.exprStmts.get(st.at).value);
        if (e.op == Op.Assignment && !self.noteAlias(a, e)) {
            p: Sym = forPointerOf(a, e.left);
            if (p != NO_SYM) { self.alias.put(nameOf(p), e.right); }
            // `$forsK = xs.asSlice()`: a loop over a type viewed as a slice walks `xs`.
            v: Sym = forViewOf(a, e.left);
            if (v != NO_SYM) {
                r: Expr = a.expr(e.right);
                match r.payload {
                    Call(c) { if (a.calls.get(c).receiver != NO_NODE) { self.alias.put(nameOf(v), a.calls.get(c).receiver); } }
                    _ { }
                }
            }
        }
    }

    holdScan &self inout a:Ast b:long -> void {
        if (b < 0) { return; }
        for k in 0..a.blockLen(b) {
            st: Stmt = a.stmtAt(b, k);
            self.holdNote(a, st);
            if (st.kind == StmtKind.While) {
                w: WhileNode = a.whiles.get(st.at);
                p: Sym = forLoopPtr(a, w.body);
                if (p != NO_SYM) {
                    was: long = a.enterStmt(a.stmtIdAt(b, k));
                    self.holdLoop(a, w.body, p);
                    gPos = was;
                }
            }
            kids: Vec<long> = childBlocks(a, st);
            for j in 0..kids.len() { self.holdScan(a, kids.get(j)); }
        }
    }

    holdLoop &self inout a:Ast body:long p:Sym -> void {
        src: Option<NodeId> = self.alias.find(nameOf(p));
        setup: NodeId = NO_NODE;
        match src { Some(s) { setup = s; } None { return; } }
        path: Vec<Sym>;
        xs: NodeId = forContainer(a, setup);
        // Through the slice an `AsSlice` type handed the loop, to the collection itself.
        vs: Sym = forViewOf(a, xs);
        if (vs != NO_SYM) {
            hit: Option<NodeId> = self.alias.find(nameOf(vs));
            match hit { Some(r) { xs = r; } None { } }
        }
        if (!self.holdPath(a, xs, NO_SYM, &path)) { return; }
        shownXs: str = self.spoken(a, xs, "");
        // A slice is a read-only view unless it is an `inout` parameter (`checkSliceStore`), and
        // lending its elements to the loop is writing through it.
        if (forLends(p) && a.expr(xs).kind == Lit.Slice && !self.inoutParam(a, xs)) {
            failStr(format("`for x in &{}` writes through the slice '{}', which is a read-only view unless it is an `inout` parameter -- declare it `inout {}:[T]` and lend it with '&' at the call",
                           shownXs, shownXs, shownXs));
        }
        d: VarDeclNode = a.decls.get(a.stmtAt(body, 0).at);
        self.hx = d.name;
        self.hRef = d.kind == Lit.Ref;
        self.hLend = forLends(p);
        self.hPath = path;
        self.hShown = shownXs;
        // A `var` global walked: a function the body calls may write it by name, which no
        // argument shows (`for x in G { refill(); }`).
        self.hGlobal = NO_SYM;
        if (isVarGlobalName(self.hPath.get(0))) { self.hGlobal = self.hPath.get(0); }
        self.holdNote(a, a.stmtAt(body, 0));
        self.holdNote(a, a.stmtAt(body, 1));
        self.holdFrom(a, body, 2);    // past the element's declaration and fetch
    }

    // Is `id` a bare `inout` parameter of the function being held?
    inoutParam &self inout a:Ast id:NodeId -> bool {
        e: Expr = a.expr(id);
        if (e.op != Op.Lvalue || self.hFn < 0) { return false; }
        n: Sym = NO_SYM;
        match e.payload { Name(x) { n = x; } _ { return false; } }
        f: FnNode = a.fns.get(self.hFn);
        for k in 0..f.argCount {
            p: VarDeclNode = a.paramAt(f, k);
            if (p.name == n) { return p.conv == Conv.Inout; }
        }
        return false;
    }

    holdBlock &self inout a:Ast b:long -> void {
        if (b < 0) { return; }
        self.holdFrom(a, b, 0);
    }

    // A block's statements from `start`. The releases the ownership pass put ahead of a `return`
    // (every open scope's, the collection's own included when the loop walks a value the function
    // owns) are not the body's: the loop is abandoned before they run, so they change nothing it
    // reads. A `break` releases only scopes inside the loop, and a `?` is a `return`.
    holdFrom &self inout a:Ast b:long start:long -> void {
        n: long = a.blockLen(b);
        skipFrom: long = n;
        skipTo: long = n;
        r: long = start;
        while (r < n && a.stmtAt(b, r).kind != StmtKind.Return) { r = r + 1; }
        if (r < n) {
            skipTo = r;
            skipFrom = r;
            while (skipFrom > start && exitDrop(a, a.stmtAt(b, skipFrom - 1))) { skipFrom = skipFrom - 1; }
        }
        k: long = start;
        while (k < n) {
            self.holdNote(a, a.stmtAt(b, k));
            if (k >= skipFrom && k < skipTo) { k = k + 1; continue; }
            w: long = a.enterStmt(a.stmtIdAt(b, k));
            self.holdStmt(a, a.stmtAt(b, k));
            gPos = w;
            k = k + 1;
        }
    }

    holdStmt &self inout a:Ast st:Stmt -> void {
        if (st.kind == StmtKind.VarDecl) { self.holdExpr(a, a.decls.get(st.at).init); return; }
        if (st.kind == StmtKind.Expr || st.kind == StmtKind.Call) { self.holdExpr(a, a.exprStmts.get(st.at).value); return; }
        if (st.kind == StmtKind.Return) { self.holdExpr(a, a.returns.get(st.at).value); return; }
        if (st.kind == StmtKind.If) {
            at: long = st.at;
            while (at >= 0) {
                br: IfNode = a.ifs.get(at);
                self.holdExpr(a, br.cond);
                self.holdBlock(a, br.body);
                at = br.elseIf;
            }
            return;
        }
        if (st.kind == StmtKind.While) {
            w: WhileNode = a.whiles.get(st.at);
            self.holdExpr(a, w.cond); self.holdBlock(a, w.body); self.holdBlock(a, w.step);
            return;
        }
        if (st.kind == StmtKind.Loop || st.kind == StmtKind.Block || st.kind == StmtKind.Unsafe) {
            self.holdBlock(a, a.blockStmts.get(st.at).body);
            return;
        }
        if (st.kind == StmtKind.Match) {
            m: MatchNode = a.matches.get(st.at);
            for k in 0..m.armCount {
                self.holdExpr(a, a.arms.get(m.firstArm + k).test);
                self.holdBlock(a, a.arms.get(m.firstArm + k).body);
            }
            return;
        }
        if (st.kind == StmtKind.With) {
            w: WithNode = a.withs.get(st.at);
            self.holdName(a, w.name, "held by `with`, which writes it");
            self.holdBlock(a, w.body);
            return;
        }
        if (st.kind == StmtKind.Destructure) { self.holdExpr(a, a.destructures.get(st.at).value); return; }
        if (st.kind == StmtKind.Asm) {
            n: AsmNode = a.asms.get(st.at);
            for k in 0..n.pieceCount {
                pc: AsmPiece = a.asmPieces.get(n.firstPiece + k);
                if (pc.kind == AsmKind.In) { self.holdWrite(a, pc.value, "handed to an `asm` block, which may write it"); }
                if (pc.kind == AsmKind.Out) { self.holdName(a, pc.name, "written by an `asm` block's `out`"); }
            }
        }
    }

    holdName &self inout a:Ast n:Sym how:str -> void {
        if (n == NO_SYM) { return; }
        self.holdWrite(a, a.leafOf(Op.Lvalue, Payload.Name(n), Lit.Void, NO_SYM), how);
    }

    holdExpr &self inout a:Ast id:NodeId -> void {
        if (id == NO_NODE) { return; }
        e: Expr = a.expr(id);
        if (e.op == Op.Assignment) {
            l: Expr = a.expr(e.left);
            // What the desugars write is not a write of anything: a loop's own pointer, the slice
            // an `AsSlice` loop views its collection through (`$forsK = xs.asSlice()`, which
            // names `xs` only as the alias `holdNote` just made: the call is judged below, by
            // what `asSlice` writes), and a borrow local bound to its place.
            bound: bool = l.op == Op.Lvalue && l.kind == Lit.Ref && a.expr(e.right).op == Op.AddressOf;
            if (forPointerOf(a, e.left) == NO_SYM && forViewOf(a, e.left) == NO_SYM && !bound) {
                self.holdWrite(a, e.left, "assigned to");
                self.holdMove(a, e.right);
            }
            self.holdExpr(a, e.left);
            // A borrow local's `&place` names the place, and lends nothing: what is written
            // through the local is followed to the place by `holdPath`.
            if (bound) {
                r: Expr = a.expr(e.right);
                match r.payload { Sub(v) { self.holdExpr(a, v); } _ { } }
                return;
            }
            self.holdExpr(a, e.right);
            return;
        }
        if (e.left != NO_NODE) { self.holdExpr(a, e.left); self.holdExpr(a, e.right); return; }
        if (e.op == Op.FunctionCall || e.op == Op.MethodCall) {
            c: CallNode = a.calls.get(0);
            match e.payload { Call(i) { c = a.calls.get(i); } _ { } }
            nodes: Vec<NodeId>;
            if (c.receiver != NO_NODE) { nodes.push(c.receiver); }
            for k in 0..c.argCount { nodes.push(a.argAt(c, k)); }
            if (self.hGlobal != NO_SYM && self.callWritesGlobal(a, c, self.hGlobal)) {
                failStr(format("'{}' is written by '{}', which this body calls inside `for {} in {}`, which walks it -- the loop reads its elements in place, so nothing it calls may change it; collect the changes and make them after the loop",
                               self.hShown, calledName(c), spokenName(self.hx), self.hShown));
            }
            for k in 0..nodes.len() {
                if (self.holdCalleeWrites(a, c, k)) {
                    // Only where the callee writes: `self.err()` bumping `self.errors` leaves the
                    // `self.cur.attrs` a loop walks alone.
                    // Asked only where it can matter: an argument that is a strict prefix of the
                    // walked path (`self` for `self.cur.attrs`). Anything else is all or nothing.
                    how: str = keepString(format("handed to '{}', which writes it", calledName(c)));
                    np: Vec<Sym>;
                    if (self.holdPath(a, nodes.get(k), self.hx, &np) && np.get(0) != self.hx
                        && np.len() < self.hPath.len() && pathsOverlap(np, self.hPath)) {
                        qs: Vec<Sym> = self.calleePaths(a, c, k);
                        for q in qs { self.holdWriteAt(a, nodes.get(k), q, how); }
                    } else { self.holdWrite(a, nodes.get(k), how); }
                }
                if (self.holdCalleeTakes(a, c, k)) { self.holdMove(a, nodes.get(k)); }
                self.holdExpr(a, nodes.get(k));
            }
            self.holdExpr(a, c.callee);
            return;
        }
        match e.payload {
            Sub(v) {
                if (e.op == Op.AddressOf && e.kind != Lit.Fn) { self.holdWrite(a, v, "lent with `&`, which allows writing it"); }
                self.holdExpr(a, v);
            }
            Field(i) { self.holdExpr(a, a.fields.get(i).base); }
            Index(i) {
                ix: IndexNode = a.indexes.get(i);
                self.holdExpr(a, ix.base); self.holdExpr(a, ix.index);
                self.holdExpr(a, ix.sliceStart); self.holdExpr(a, ix.sliceEnd);
            }
            Lit(i) {
                l: LitNode = a.lits.get(i);
                for k in 0..l.initCount { self.holdExpr(a, a.inits.get(l.firstInit + k).value); }
                self.holdExpr(a, l.rest);
            }
            _ { }
        }
    }

    // A write to `place`: refused when it is the collection or part of it, and, in the plain
    // form, when it is a struct element through `x`.
    holdWrite &self inout a:Ast place:NodeId how:str -> void {
        self.holdWriteAt(a, place, intern(""), how);
    }

    // The same for a write at `below` under `place` (`cur.name`; "" for all of it).
    holdWriteAt &self inout a:Ast place:NodeId below:Sym how:str -> void {
        path: Vec<Sym>;
        if (!self.holdPath(a, place, self.hx, &path)) { return; }
        shown: str = self.spoken(a, place, "");      // the place as the source names it
        appendFields(&path, nameOf(below));
        if (path.get(0) == self.hx) {
            if (!self.hRef) { return; }          // a scalar element is the loop's own copy
            if (path.len() == 1 && how == "assigned to") {
                failStr(format("cannot assign to '{}': it is a borrow of an element of {} -- assign to its fields, or write the element by index",
                               spokenName(self.hx), self.hShown));
            }
            if (!self.hLend) {
                failStr(format("'{}' is {}, but in `for {} in {}` an element is read-only -- write `for {} in &{}` to change the elements",
                               shown, how, spokenName(self.hx), self.hShown,
                               spokenName(self.hx), self.hShown));
            }
            return;
        }
        if (pathsOverlap(path, self.hPath)) {
            failStr(format("'{}' is {} inside `for {} in {}`, which walks it -- the loop reads its elements in place, so the body may not change it; collect the changes and make them after the loop",
                           shown, how, spokenName(self.hx), self.hShown));
        }
    }

    // `place` moved out: refused when it is the collection or part of it.
    holdMove &self inout a:Ast place:NodeId -> void {
        if (place == NO_NODE) { return; }
        e: Expr = a.expr(place);
        if (e.op != Op.Lvalue && e.op != Op.FieldAccess) { return; }
        if (e.kind != Lit.Struct || !gReg.needsDrop(e.structName)) { return; }
        path: Vec<Sym>;
        if (!self.holdPath(a, place, self.hx, &path) || path.get(0) == self.hx) { return; }
        if (pathsOverlap(path, self.hPath)) {
            failStr(format("'{}' is moved inside `for {} in {}`, which walks it -- the loop reads its elements in place",
                           self.spoken(a, place, ""), spokenName(self.hx), self.hShown));
        }
    }

    // Through a fn value the type is the whole contract: it lends, or takes (`sink`), and never
    // writes what it lends. Anything else is the write mask's to say.
    holdCalleeWrites &self inout a:Ast c:CallNode pos:long -> bool {
        if (c.slot == SLOT_FNPTR || c.callee != NO_NODE) { return false; }
        return self.calleeWrites(a, c, pos);
    }

    holdCalleeTakes &self inout a:Ast c:CallNode pos:long -> bool {
        if (c.slot == SLOT_FNPTR || c.callee != NO_NODE) {
            at: long = gFnSigs.find(c.sigKey);
            if (at < 0) { return false; }
            sig: FnSig = gFnSigs.sigAt(at);
            if (pos >= sig.paramCount) { return false; }
            return gFnSigs.paramAt(sig, pos).conv == Conv.Sink;
        }
        if (c.slot != NO_SLOT) { return false; }
        hit: Option<long> = self.fnAt.find(nameOf(c.name));
        match hit {
            Some(i) {
                f: FnNode = a.fns.get(i);
                if (pos >= f.argCount) { return false; }
                p: VarDeclNode = a.paramAt(f, pos);
                return p.kind == Lit.Struct && p.conv == Conv.Sink;
            }
            None { }
        }
        return false;
    }

    // The place an expression names, root first, through borrow locals and loop pointers to what
    // they point into: a field adds its name, an index `*` (any element), a call yielding a borrow
    // or a pointer the place of its receiver (or first argument with one) and `*`. `stop` is
    // taken as it is, not followed: the loop's own `x`. False for anything that is not a place.
    // A place as the source spells it, for a message: `holdPath`'s walk, following an alias only
    // through the compiler's own hidden locals (a loop's view `$forsK`, a match's `$matchN`), so
    // a binding the user named (`args` in `Call(args)`) is said by that name rather than as the
    // payload slot it borrows. `below` adds fields under it.
    spoken &self inout a:Ast id:NodeId below:str -> str {
        out: Vec<Sym>;
        if (!self.spokenPath(a, id, &out)) { return "this value"; }
        appendFields(&out, below);
        return pathText(out);
    }

    spokenPath &self inout a:Ast id:NodeId inout out:Vec<Sym> -> bool {
        if (id == NO_NODE) { return false; }
        e: Expr = a.expr(id);
        if (e.op == Op.Lvalue) {
            n: Sym = NO_SYM;
            match e.payload { Name(x) { n = x; } _ { return false; } }
            if (isHiddenName(n)) {
                src: Option<NodeId> = self.alias.find(nameOf(n));
                match src { Some(s) { return self.spokenPath(a, s, out); } None { } }
            }
            out.push(n);
            return true;
        }
        if (e.op == Op.FunctionCall || e.op == Op.MethodCall) {
            c: CallNode = a.calls.get(0);
            match e.payload { Call(i) { c = a.calls.get(i); } _ { return false; } }
            if (self.spokenPath(a, c.receiver, out)) { out.push(intern("*")); return true; }
            for k in 0..c.argCount {
                if (self.spokenPath(a, a.argAt(c, k), out)) { out.push(intern("*")); return true; }
            }
            return false;
        }
        match e.payload {
            Sub(v) { return self.spokenPath(a, v, out); }
            Field(f) {
                fd: FieldNode = a.fields.get(f);
                if (!self.spokenPath(a, fd.base, out)) { return false; }
                out.push(fd.name);
                return true;
            }
            Index(i) {
                ix: IndexNode = a.indexes.get(i);
                if (ix.base != NO_NODE) {
                    if (!self.spokenPath(a, ix.base, out)) { return false; }
                } else { out.push(ix.name); }
                out.push(intern("*"));
                return true;
            }
            _ { }
        }
        return false;
    }

    holdPath &self inout a:Ast id:NodeId stop:Sym inout out:Vec<Sym> -> bool {
        if (id == NO_NODE) { return false; }
        e: Expr = a.expr(id);
        if (e.op == Op.Lvalue) {
            n: Sym = NO_SYM;
            match e.payload { Name(x) { n = x; } _ { return false; } }
            if (n != stop) {
                src: Option<NodeId> = self.alias.find(nameOf(n));
                match src { Some(s) { return self.holdPath(a, s, stop, out); } None { } }
            }
            out.push(n);
            return true;
        }
        if (e.op == Op.FunctionCall || e.op == Op.MethodCall) {
            if (e.kind != Lit.Ref && e.kind != Lit.Ptr && e.kind != Lit.Slice) { return false; }
            c: CallNode = a.calls.get(0);
            match e.payload { Call(i) { c = a.calls.get(i); } _ { return false; } }
            if (self.holdPath(a, c.receiver, stop, out)) { out.push(intern("*")); return true; }
            for k in 0..c.argCount {
                if (self.holdPath(a, a.argAt(c, k), stop, out)) { out.push(intern("*")); return true; }
            }
            return false;
        }
        match e.payload {
            Sub(v) { return self.holdPath(a, v, stop, out); }
            Field(f) {
                fd: FieldNode = a.fields.get(f);
                if (!self.holdPath(a, fd.base, stop, out)) { return false; }
                out.push(fd.name);
                return true;
            }
            Index(i) {
                ix: IndexNode = a.indexes.get(i);
                if (ix.base != NO_NODE) {
                    if (!self.holdPath(a, ix.base, stop, out)) { return false; }
                } else { out.push(ix.name); }
                out.push(intern("*"));
                return true;
            }
            _ { }
        }
        return false;
    }
}

// The first `limit` fields of `q` (`a.b.c`), after a `.` when `out` has any.
local pushFields inout out:String q:str limit:long -> void {
    n: long = 1;
    for k in 0..q.len {
        if (charAt(q, k) == '.') {
            if (n == limit) { break; }
            n = n + 1;
        }
        if (k == 0 && out.len > 0) { out.push('.'); }
        out.push(charAt(q, k) as char);
    }
}

// `out` followed by the fields `below` names (`cur.name`).
local appendFields inout out:Vec<Sym> below:str -> void {
    start: long = 0;
    for k in 0..below.len + 1 {
        if (k == below.len || charAt(below, k) == '.') {
            if (k > start) { out.push(intern(strSlice(below, start, k - start))); }
            start = k + 1;
        }
    }
}

// The expressions a statement evaluates itself (not those of the blocks it holds).
local stmtExprs inout a:Ast st:Stmt -> Vec<NodeId> {
    out: Vec<NodeId>;
    if (st.kind == StmtKind.VarDecl) { out.push(a.decls.get(st.at).init); }
    else if (st.kind == StmtKind.Expr || st.kind == StmtKind.Call) { out.push(a.exprStmts.get(st.at).value); }
    else if (st.kind == StmtKind.Return) { out.push(a.returns.get(st.at).value); }
    else if (st.kind == StmtKind.If) {
        at: long = st.at;
        while (at >= 0) { br: IfNode = a.ifs.get(at); out.push(br.cond); at = br.elseIf; }
    } else if (st.kind == StmtKind.While) { out.push(a.whiles.get(st.at).cond); }
    else if (st.kind == StmtKind.Match) {
        m: MatchNode = a.matches.get(st.at);
        for k in 0..m.armCount { out.push(a.arms.get(m.firstArm + k).test); }
    } else if (st.kind == StmtKind.Destructure) { out.push(a.destructures.get(st.at).value); }
    return out;
}

// A `var` global's name.
local isVarGlobalName n:Sym -> bool {
    gi: long = gReg.findGlobal(nameOf(n));
    return gi >= 0 && gReg.globalDef(gi).isVar;
}

// The statements' blocks a statement holds, for a walk that only looks for something in them.
// The argument at `pos` of a call through a fn value crosses as a copy that no callee can write
// the caller's value through: a scalar, or a `str` (a view whose bytes are never written), or a
// fn value. Asked of the fn type's parameter when the call knows its signature, of the argument's
// own type otherwise. A struct or a slice is not answered for: the fn type says only lend or
// `sink`, and a function writing an `inout` parameter is accepted behind a lending type.
local fnValueArgPlain inout a:Ast c:CallNode pos:long -> bool {
    k: Lit = Lit.Void;
    si: long = gFnSigs.find(c.sigKey);
    if (si >= 0) {
        sig: FnSig = gFnSigs.sigAt(si);
        if (pos < sig.paramCount) { k = gFnSigs.paramAt(sig, pos).kind; }
    }
    if (k == Lit.Void && pos < c.argCount) { k = a.expr(a.argAt(c, pos)).kind; }
    return isInteger(k) || k == Lit.Bool || k == Lit.Char || k == Lit.Float || k == Lit.Double
           || k == Lit.Str || k == Lit.Fn;
}

local childBlocks inout a:Ast st:Stmt -> Vec<long> {
    out: Vec<long>;
    if (st.kind == StmtKind.If) {
        at: long = st.at;
        while (at >= 0) { br: IfNode = a.ifs.get(at); out.push(br.body); at = br.elseIf; }
    } else if (st.kind == StmtKind.While) {
        w: WhileNode = a.whiles.get(st.at);
        out.push(w.body);
        out.push(w.step);
    } else if (st.kind == StmtKind.Loop || st.kind == StmtKind.Block || st.kind == StmtKind.Unsafe) {
        out.push(a.blockStmts.get(st.at).body);
    } else if (st.kind == StmtKind.With) {
        out.push(a.withs.get(st.at).body);
    } else if (st.kind == StmtKind.Match) {
        m: MatchNode = a.matches.get(st.at);
        for k in 0..m.armCount { out.push(a.arms.get(m.firstArm + k).body); }
    }
    return out;
}

// `$forsK`, the slice a `for` over an `AsSlice` type holds (`Parser.parseForEach`), or NO_SYM.
local forViewOf inout a:Ast id:NodeId -> Sym {
    e: Expr = a.expr(id);
    if (e.op != Op.Lvalue) { return NO_SYM; }
    match e.payload {
        Name(n) { if (strStartsWith(nameOf(n), "$fors")) { return n; } }
        _ { }
    }
    return NO_SYM;
}

// The collection a loop's pointer was set from: `xs.ptr` (a slice, or the view `$forsK` an
// `AsSlice` type hands back), `xs[..].ptr` (an array), as `Parser.parseForEach` writes them.
local forContainer inout a:Ast setup:NodeId -> NodeId {
    at: NodeId = setup;
    s: Expr = a.expr(at);
    match s.payload { Field(f) { at = a.fields.get(f).base; } _ { return at; } }
    e: Expr = a.expr(at);
    match e.payload {
        Index(i) { if (a.indexes.get(i).whole) { return a.indexes.get(i).base; } }
        _ { }
    }
    return at;
}

// Two places overlap when one contains the other: the same root, and each step the same field
// or an element of either.
local pathsOverlap p:Vec<Sym> q:Vec<Sym> -> bool {
    if (p.len() == 0 || q.len() == 0 || p.get(0) != q.get(0)) { return false; }
    n: long = p.len();
    if (q.len() < n) { n = q.len(); }
    for k in 1..n {
        x: str = nameOf(p.get(k));
        y: str = nameOf(q.get(k));
        if (x != "*" && y != "*" && x != y) { return false; }
    }
    return true;
}

// A callee as the source spelled it: a method by its own name (`push`, not `vec::Vec_long_push`,
// which is what the checker resolved it to), a function by its bare one.
local calledName c:CallNode -> str {
    s: str = lastComponentOf(nameOf(c.name));
    if (c.receiver == NO_NODE) { return s; }
    k: long = s.len - 1;
    while (k > 0 && charAt(s, k) != '_') { k = k - 1; }
    if (k > 0) { return strSlice(s, k + 1, s.len - k - 1); }
    return s;
}

// A variable as it was written: a shadowing declaration's rename (`x$3`) without its number.
local spokenName n:Sym -> str {
    s: str = lastComponentOf(nameOf(n));
    for k in 1..s.len {
        if (charAt(s, k) == '$') { return strSlice(s, 0, k); }
    }
    return s;
}

// A path as the source would spell it: a renamed local by its name, a tuple's element as `.0`,
// an element as `[..]`. A variant's payload has no spelling of its own (a `match` binds it to a
// name, which `spoken` prefers), so it is said as one: `e.Call.0` is payload 0 of `e` as a `Call`.
// A hidden local left at the root is said for what it holds.
local pathText p:Vec<Sym> -> str {
    s: String;
    for k in 0..p.len() {
        c: str = nameOf(p.get(k));
        if (k == 0) { s.pushStr(rootText(p.get(k))); }
        else if (c == "*") { s.pushStr("[..]"); }
        else { s.push('.'); s.pushStr(componentText(c)); }
    }
    return keepString(s);
}

// `$Call$0` (a payload slot) as `Call.0`, `$1` (a tuple's element) as `1`.
local componentText c:str -> str {
    if (c.len < 2 || charAt(c, 0) != '$') { return c; }
    for k in 1..c.len {
        if (charAt(c, k) == '$') {
            s: String;
            s.pushStr(strSlice(c, 1, k - 1));
            s.push('.');
            s.pushStr(strSlice(c, k + 1, c.len - k - 1));
            return keepString(s);
        }
    }
    return strSlice(c, 1, c.len - 1);
}

// A path's root: a local by the name it was declared with, a hidden local by what it holds.
local rootText n:Sym -> str {
    if (!isHiddenName(n)) { return spokenName(n); }
    s: str = nameOf(n);
    if (strStartsWith(s, "$fors") || strStartsWith(s, "$forp")) { return "the collection the loop walks"; }
    if (strStartsWith(s, "$bmatch") || strStartsWith(s, "$match")) { return "the value being matched"; }
    if (strStartsWith(s, "$try")) { return "the value `?` reads"; }
    return "a temporary";
}

// A local the compiler wrote, which the source never names: `$matchN`, `$forsK`, `$tupN`, ...
local isHiddenName n:Sym -> bool {
    s: str = lastComponentOf(nameOf(n));
    return s.len > 0 && (charAt(s, 0) == '$' || charAt(s, 0) == '<');
}

// A parameter the caller's value is reached through: a borrow, a pointer, a view. A by-value
// struct or scalar is the callee's own copy, and writing it touches nothing of the caller's.
local throughParam p:VarDeclNode -> bool {
    return p.kind == Lit.Ref || p.kind == Lit.Ptr || p.kind == Lit.Str || p.kind == Lit.Slice || p.isArray;
}

// Whether an assignment target reaches its place through a raw pointer -- a dereference, or
// an index on a pointer, a `str` or a slice -- which may be anything at all.
local throughPointer inout a:Ast id:NodeId -> bool {
    at: NodeId = id;
    while (at != NO_NODE) {
        e: Expr = a.expr(at);
        // `*p` of a lent parameter (`lentPlaceOf`) is the parameter's place, followed like a field.
        if (e.op == Op.Deref && lentPlaceOf(a, at) == NO_NODE) { return true; }
        next: NodeId = NO_NODE;
        match e.payload {
            Field(i) { next = a.fields.get(i).base; }
            Index(i) {
                ix: IndexNode = a.indexes.get(i);
                if (ix.rawPointerBase) { return true; }
                if (ix.base != NO_NODE) {
                    bk: Lit = a.expr(ix.base).kind;
                    if (bk == Lit.Ptr || bk == Lit.Str || bk == Lit.Slice) { return true; }
                }
                next = ix.base;
            }
            Sub(v) { next = v; }
            _ { }
        }
        at = next;
    }
    return false;
}

// `s.ptr` or `s.len` of a `str`: one of its two words, copied out. Handing either to a call writes
// nothing of `s`'s: a `str`'s bytes are never written by safe code, and a write through the raw
// pointer in `unsafe` is the author's word (into an immutable global's bytes, it faults, as every
// write `unsafe` smuggles past this guard does). `putStr(w, HEX[d..d+1])` was refused because
// `putStr` hands `s.ptr` to `Write.write`. A slice's `.ptr` still counts: a slice's elements are
// writable.
local strWord inout a:Ast id:NodeId -> bool {
    if (id == NO_NODE) { return false; }
    e: Expr = a.expr(id);
    if (e.op != Op.FieldAccess) { return false; }
    match e.payload {
        Field(i) {
            f: FieldNode = a.fields.get(i);
            if (a.expr(f.base).kind != Lit.Str) { return false; }
            return nameOf(f.name) == "ptr" || nameOf(f.name) == "len";
        }
        _ { }
    }
    return false;
}

// A release the ownership pass writes (`Checker.ownDropOf`): `x.drop()` on a bare name, called as
// `T_drop`, alone or under its flag (`if (__moved_x == 0) { ... }`, `ownGuardedDrop`).
local exitDrop inout a:Ast st:Stmt -> bool {
    if (st.kind == StmtKind.If) {
        nd: IfNode = a.ifs.get(st.at);
        if (nd.elseIf >= 0 || a.blockLen(nd.body) != 1) { return false; }
        return exitDrop(a, a.stmtAt(nd.body, 0));
    }
    if (st.kind != StmtKind.Expr) { return false; }
    e: Expr = a.expr(a.exprStmts.get(st.at).value);
    if (e.op != Op.MethodCall) { return false; }
    c: CallNode = a.calls.get(0);
    match e.payload { Call(i) { c = a.calls.get(i); } _ { return false; } }
    if (c.argCount != 0 || c.receiver == NO_NODE || a.expr(c.receiver).op != Op.Lvalue) { return false; }
    return strEndsWith(nameOf(c.name), "_drop");
}

local isImmutableGlobal n:Sym -> bool {
    gi: long = gReg.findGlobal(nameOf(n));
    if (gi < 0) { return false; }
    return !gReg.globalDef(gi).isVar;
}
local refuse g:Sym why:str -> void {
    failStr(format("'{}' is immutable, and here it {} -- declare it `var {}: ...` if it is meant to change", nameOf(g), why, lastComponentOf(nameOf(g))));
}
local refuseStr g:Sym why:String -> void { unsafe { refuse(g, why.view()); } }
