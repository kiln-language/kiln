// The immutability guard makes sure a global not declared `var` is never written after the
// compiler has computed it.
//
// A write is more than an assignment, so the guard first decides, per function, which
// by-reference parameters a body writes through (a fixpoint over the call graph), and then holds
// every use of a constant to that. A write smuggled through `unsafe` faults at runtime instead,
// because a constant is emitted into `.rodata`.
//
// The same write masks decide what a `for x in xs` loop body and a borrowing match arm may call
// while they hold a collection or a payload, so those holds live here too.
#include <support::compiler>
#include <parse::{ast, registry, types, upstream}>
#include <{eval, facts}>
#include <stdlib::{fmt, io, map, mem, option, string, time, vec}>

local WRITES_ALL: long = 4611686018427387904;   // bit 62: a store through a raw pointer, or `asm`
// A `DepFact` that is no parameter's: the function calls a fn value, or dispatches the trait's slot.
local CB_FNVALUE: long = -2;
local CB_DISPATCH: long = -1;

// The part of a `var` global a question about writers is asked of: the global, the fields below
// it (a run of `ConstGuard.gpFields`; none for all of it), and the key its answers are kept
// under, which for all of it is the global's own name. A function writing `gReg.count` does not
// write `gReg.items`, and one writing `gReg` writes both.
pub struct GPlace { key: Sym, root: Sym, first: long, count: long }

// How many of `path`'s steps after its root are fields: up to its first step that is not one (an
// element or a call's borrow stands for all of what holds it).
local fieldSteps path:Vec<Sym> -> long {
    star: Sym = intern("*");
    k: long = 1;
    while (k < path.len() && path.get(k) != star) { k = k + 1; }
    return k - 1;
}

pub struct ConstGuard {
    fnAt: HashMap<long, long>,      // resolved name -> `fns` index
    writes: Vec<long>,             // per function: bit k = writes through parameter k
    paramIx: HashMap<long, long>,   // the function being scanned: parameter name -> index
    mask: long,                    // and the bits found so far
    changed: bool,
    // In a package build, which parameters each function hands, through calls, to a trait
    // dispatch, and where. Whether such a call writes depends on every implementation in the
    // final program, and a dependent may add more, so the question is written into the facts for
    // the dependent to answer again. Each function has a chain of these through flat arrays.
    cur: long,
    deps: Vec<DepFact>,
    depNext: Vec<long>,
    depHead: Vec<long>,
    depKeys: HashMap<str, bool>,
    // A borrow local the checker bound to a place (`r = &subject.$V$k`, a match through a
    // borrow): writing through it writes that place, so its root is the place's root.
    alias: HashMap<long, NodeId>,
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
    // and the fields below each written global, a run in `gfWFields` (none for all of it)
    gfWFirst: Vec<long>,
    gfWCount: Vec<long>,
    gfWFields: Vec<Sym>,
    gfCHead: Vec<long>,            // its callees (-1: any addressed function), a chain through `gfC`
    gfC: Vec<long>,
    gfCNext: Vec<long>,
    // and the parts of `var` globals it names at all, read or written, a chain through `gfR`,
    // with the fields below each in `gfWFields` as a write's are. What a call lent a global
    // `inout` may not reach.
    gfRHead: Vec<long>,
    gfR: Vec<Sym>,
    gfRNext: Vec<long>,
    gfRFirst: Vec<long>,
    gfRCount: Vec<long>,
    touchedAt: long,               // what `touchesHere` found: the record,
    touchedRead: bool,             // and whether it is a read's
    touchPath: Vec<long>,          // and the functions from it back to where the walk began
    gfCur: long,
    gfAddr: Vec<long>,             // the addressed functions, by index, once asked
    gfAddrSig: Vec<Sym>,           // and the fn type each was addressed as (NO_SYM: at none, read back raw)
    gfVtab: Vec<long>,             // every function placed in a vtable, by index, once asked
    gfVtabDone: bool,
    gfFan: Vec<long>,              // per edge below 0, the functions it reaches (`fanOut`), as runs
    gfFanAt: HashMap<long, long>,
    gfFanN: HashMap<long, long>,
    gfAddrDone: bool,
    gfMemoAt: HashMap<long, long>,  // per global, where its run of `gfMemo` starts
    gfMemo: Vec<long>,             // 0 unknown, 1 writes, 2 does not, 3 met in the current query
    gfTouched: Vec<long>,          // what the current query marked 3
    gfUs: long,                    // time spent answering, for `--time-phases`
    hGlobal: Sym,                  // the `var` global a loop being held walks, or NO_SYM
    hPlace: GPlace,                // and the part of it the loop walks
    gpFields: Vec<Sym>,            // the fields of every `GPlace` asked about
    // A finer answer under each bit of `writes`: which fields of that parameter the function
    // writes. It is asked only for a call a held loop's body makes (`calleePaths`), and kept once
    // answered, as a chain per function of (parameter, path) entries. A path is the fields' names
    // joined by `.` (`cur.name`), or "" for the whole parameter. This is what lets `self.err()`
    // inside `for a in self.cur.attrs` count as writing `self.errors` rather than all of `self`.
    // A path is cut at the first step that is not a field (an element, a call's borrow, a
    // dereference) and after WP_DEPTH fields. A shorter path stands for everything under it, so
    // cutting only ever claims more. A callee met while its own answer is still being worked out
    // (recursion) answers "all of it".
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
    wpIx: HashMap<long, long>,      // the walked function's parameters, as `paramIx`
    wpAlias: HashMap<long, NodeId>, // and its borrow locals, as `alias`
    ppCut: bool,                   // `paramPlace` stopped at a step that is not a field
    ppDepth: long,                 // and how many fields it named
    // A `var` global may be lent to a function that walks the parameter it lands in
    // (`for x in xs`) while calling something that writes the global by name, and then the walk's
    // view goes stale. To catch that, each function and parameter (key `f * 64 + k`) gets a chain
    // of what happens to it: a call made while a loop holds it (kind 0), or the parameter handed
    // on to position `pos` of a call (kind 1). Each call that lends a `var` global is kept as
    // well, and judged once every function's chain is known.
    hParam: long,                  // the parameter of `hFn` the loop being held walks, or -1
    phHead: HashMap<long, long>,
    phKind: Vec<long>,
    phCall: Vec<long>,
    phPos: Vec<long>,
    phNext: Vec<long>,
    lendCall: Vec<long>,           // the call (index into `calls`), the argument's position,
    lendPos: Vec<long>,
    lendG: Vec<GPlace>,            // the part of a global lent,
    lendAt: Vec<long>,             // where the call stands, and in which function
    lendFn: Vec<Sym>,
    lendWalkable: Vec<bool>,       // and whether the argument could be walked (the walk rule asks only then)
    phMemo: HashMap<long, long>,   // (global, function, parameter): 1 writes, 2 does not, 3 met now
    phTouched: Vec<long>,
    phBusy: bool,                  // the current query met a function still being worked out
    // The checker's copies (`gCopyBinds`) by their stores, while the write masks are worked out
    // and the copies decided: such a store names its place a second time, as a borrow's does.
    copyStore: HashMap<long, long>,
    probing: bool,                 // `writesCopy` is walking an arm: write nothing down but the mask
    // Another object may call this one's functions or be called by them (`--lib`, `--use`; the
    // driver sets it from `gOpenObject`), so a dispatch or a call through a fn value may reach code
    // compiled after this, as it may in a package build (`gKlibMode`).
    openObject: bool
}

local WP_DEPTH: long = 3;

// How a call holds an argument that names a `var` global (`lendMode`): as a copy of its own, lent
// to be read, or lent `inout`.
local LEND_COPY: long = 0;
local LEND_READ: long = 1;
local LEND_INOUT: long = 2;

methods ConstGuard for Default {
    new -> ConstGuard {
        return ConstGuard { fnAt: map![], writes: vec![], paramIx: map![], mask: 0, changed: false,
                            cur: -1, deps: vec![], depNext: vec![], depHead: vec![], depKeys: map![],
                            alias: map![], hx: NO_SYM, hRef: false, hLend: false, hPath: vec![], hShown: "", hFn: -1,
                            gfState: vec![], gfWHead: vec![], gfW: vec![], gfWNext: vec![],
                            gfWFirst: vec![], gfWCount: vec![], gfWFields: vec![], gfCHead: vec![],
                            gfC: vec![], gfCNext: vec![], gfRHead: vec![], gfR: vec![], gfRNext: vec![],
                            gfRFirst: vec![], gfRCount: vec![], touchedAt: -1, touchedRead: false, touchPath: vec![], gfCur: -1, gfAddr: vec![], gfAddrSig: vec![], gfVtab: vec![], gfVtabDone: false, gfFan: vec![], gfFanAt: map![], gfFanN: map![], gfAddrDone: false,
                            gfMemoAt: map![], gfMemo: vec![], gfTouched: vec![], gfUs: 0, hGlobal: NO_SYM,
                            hPlace: GPlace { key: NO_SYM, root: NO_SYM, first: 0, count: 0 }, gpFields: vec![],
                            wpHead: vec![], wpParam: vec![], wpPath: vec![], wpNext: vec![], wpDone: vec![],
                            wpBusy: vec![], wpStackF: vec![], wpStackP: vec![], wpNeedF: -1, wpNeedP: 0,
                            wpTarget: -1, wpOut: vec![], wpIx: map![], wpAlias: map![], ppCut: false,
                            ppDepth: 0, hParam: -1, phHead: map![], phKind: vec![], phCall: vec![],
                            phPos: vec![], phNext: vec![], lendCall: vec![], lendPos: vec![], lendG: vec![],
                            lendAt: vec![], lendFn: vec![], lendWalkable: vec![], phMemo: map![], phTouched: vec![], phBusy: false,
                            copyStore: map![], probing: false, openObject: false };
    }
}

methods ConstGuard {
    run &self inout a:Ast page:long -> void {
        self.index(a);
        for k in 0..gCopyBinds.len() { self.copyStore.put(gCopyBinds.get(k).store as long, k); }
        rounds: long = 0;
        self.changed = true;
        while (self.changed && rounds < 64) {
            self.changed = false;
            for i in 0..a.fns.len() {
                if (!a.fns.get(i).isTemplate) { self.scanFunction(a, i); }
            }
            rounds = rounds + 1;
        }
        // What each function writes through its parameters, for the back end's conventions.
        gFnWrites.clear();
        for w in self.writes { gFnWrites.push(w); }
        self.promoteCopies(a);
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
                self.hFn = -1;
                self.guardExpr(a, a.decls.get(st.at).init);
            }
        }
        self.holdLends(a);
        if (gTimePhases) {
            read: long = 0;
            for r in self.gfState { if (r) { read = read + 1; } }
            eprintln("  holding: {} ms; global writes: {} ms (bodies read: {}, globals asked about: {})", elapsedUs(hold) / 1000,
                     self.gfUs / 1000, read, self.gfMemoAt.len());
        }
    }

    // A `&self` call on a place whose payload a borrowed match arm holds (`gSelfLends`). That is
    // a read-only lend unless the method writes `self`, and then the write could release what the
    // binding points at. It is refused here because only here are the write masks known.
    holdSelfLends &self inout a:Ast -> void {
        for k in 0..gSelfLends.len() {
            s: SelfLend = gSelfLends.get(k);
            if (s.callee < 0 || s.callee >= self.writes.len()) { continue; }
            w: long = self.writes.get(s.callee);
            if (w == WRITES_ALL || (w & 1) != 0) {
                gPos = s.pos;
                enterFn(s.fnName);
                if (s.destr) {
                    failStr(format("cannot lend `{}` mutably while `{}` borrows an element of it\nnote: `{}` writes `self`, and the write could release or replace the element `{}` points at\nhelp: finish with the borrow first, or destructure a clone",
                                   s.what, nameOf(s.made), nameOf(a.fns.get(s.callee).name), nameOf(s.made)));
                }
                if (s.copy >= 0) {
                    failStr(format("cannot lend `{}` mutably while a match arm borrows `{}`\nnote: `{}` writes `self`, and the arm writes through `{}`, which makes it a borrow of the payload the write could replace\nhelp: finish with the borrow first, or match on a clone",
                                   s.what, nameOf(s.made), nameOf(a.fns.get(s.callee).name), nameOf(s.made)));
                }
                failStr(format("cannot lend `{}` mutably while a match arm borrows `{}`\nnote: `{}` writes `self`, and the write could release the payload `{}` points at\nhelp: finish with the borrow first, or match on a clone",
                               s.what, nameOf(s.made), nameOf(a.fns.get(s.callee).name), nameOf(s.made)));
            }
        }
        gSelfLends.clear();
    }

    // A borrowed match arm over a `var` global (`gHeldArms`): nothing it calls may write the global,
    // which would release or move what the arm's binding points at.
    holdArms &self inout a:Ast -> void {
        if (gHeldArms.len() == 0) { return; }
        for h in gHeldArms {
            hit: Sym = self.writingCall(a, h.body, self.placeOfPath(h.path));
            if (hit != NO_SYM) {
                gPos = h.pos;
                enterFn(h.fnName);
                if (h.destr) {
                    failStr(format("cannot change `{}` while `{}` borrows an element of it\nnote: `{}` is written by `{}`, which the code after `{}` calls, and the write could release or move what `{}` points at\nhelp: finish with the borrow first, or destructure a clone",
                                   lastComponentOf(nameOf(h.global)), nameOf(h.made), lastComponentOf(nameOf(h.global)), nameOf(hit), nameOf(h.made), nameOf(h.made)));
                }
                failStr(format("cannot change `{}` while a match arm borrows `{}`\nnote: `{}` is written by `{}`, which the arm calls, and the write could release or move what `{}` points at\nhelp: finish with the borrow first, or match on a clone",
                               lastComponentOf(nameOf(h.global)), nameOf(h.made), lastComponentOf(nameOf(h.global)), nameOf(hit), nameOf(h.made)));
            }
        }
        gHeldArms.clear();
    }

    // The first call in block `b` (or anything it holds) whose callee writes global `bit`.
    writingCall &self inout a:Ast b:long bit:GPlace -> Sym {
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
    writingCallIn &self inout a:Ast id:NodeId bit:GPlace -> Sym {
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

    // ─── which `var` globals a function writes ───────────────────────────────

    // Whether a call may write the part `g` of a global by name: its function, any implementation
    // a dispatch reaches, any addressed function for a call through a fn value or a fn-typed field.
    callWritesGlobal &self inout a:Ast c:CallNode g:GPlace -> bool {
        if (c.slot == SLOT_FNPTR || c.callee != NO_NODE) { return self.reachesWrite(a, fnValueEdge(c), g); }
        if (c.slot != NO_SLOT) {
            ts: Vec<long> = self.dispatchTargets(a, c);
            for t in ts { if (self.reachesWrite(a, t, g)) { return true; } }
            return false;
        }
        hit: Option<long> = self.fnAt.find(c.name as long);
        match hit { Some(i) { return self.reachesWrite(a, i, g); } None { } }
        return false;
    }

    // Every implementation a dispatch `c` may reach.
    dispatchTargets &self inout a:Ast c:CallNode -> Vec<long> {
        return self.slotTargets(a.expr(c.receiver).structName, c.slot);
    }
    // Every implementation of slot `slot` of the (mangled) trait `trait` this program has.
    slotTargets &self trait:Sym slot:long -> Vec<long> {
        out: Vec<long>;
        for i in 0..gReg.implCount() {
            im: TraitImplDef = gReg.implAt(i);
            if (intern(gReg.traitMangled(im.trait)) != trait) { continue; }
            ti: long = gReg.findTraitSym(im.trait.name);
            if (ti < 0) { continue; }
            t: TraitDef = gReg.traitDef(ti);
            if (slot < 0 || slot >= t.methodCount) { continue; }
            hit: Option<long> = self.fnAt.find((implMethodName(im, gReg.traitMethodAt(t, slot).name)) as long);
            match hit { Some(fi) { out.push(fi); } None { } }
        }
        return out;
    }

    // Whether function `f` (-1 for any addressed function) writes the part `g` of a global by
    // name, itself or through what it calls; the answers are kept per part (`g.key`). This is a depth-first walk of the calls from `f`, reading each function's
    // body once. A walk that finds no writer has seen everything reachable from where it started,
    // so no function it met writes `g`. A walk that finds one knows that only of the functions on
    // its path, and forgets what else it met, since a function in a cycle may have been cut short.
    reachesWrite &self inout a:Ast f:long g:GPlace -> bool { return self.reachesBy(a, f, g, false); }
    // The same for a read or a write: whether `f` names the part `g` of a global at all.
    reachesAccess &self inout a:Ast f:long g:GPlace -> bool { return self.reachesBy(a, f, g, true); }

    reachesBy &self inout a:Ast f:long g:GPlace reads:bool -> bool {
        self.gfReady(a);
        // A question about reads is kept apart from the same part's question about writes.
        key: long = g.key as long;
        if (reads) { key = 0 - key - 1; }
        base: long = -1;
        hit: Option<long> = self.gfMemoAt.find(key);
        match hit { Some(b) { base = b; } None { } }
        if (base < 0) {
            base = self.gfMemo.len();
            for i in 0..a.fns.len() { self.gfMemo.push(0); }
            self.gfMemoAt.put(key, base);
        }
        self.gfTouched.clear();
        t0: Instant = Instant { secs: 0, nanos: 0 };
        if (gTimePhases) { t0 = monotonic(); }
        found: bool = self.reachFrom(a, f, g, base, reads);
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
    reachFrom &self inout a:Ast f:long g:GPlace base:long reads:bool -> bool {
        if (f < 0) {
            at: long = self.fanOut(a, f);
            for k in 0..self.gfFanN.getOr(f, 0) {
                if (self.reachFrom(a, self.gfFan.get(at + k), g, base, reads)) { return true; }
            }
            return false;
        }
        m: long = self.gfMemo.get(base + f);
        if (m == 1) { return true; }
        if (m != 0) { return false; }
        self.gfMemo.set(base + f, 3);
        self.gfTouched.push(f);
        if (self.touchesHere(a, f, g, reads) >= 0) { self.gfMemo.set(base + f, 1); return true; }
        c: long = self.gfCHead.get(f);
        while (c >= 0) {
            if (self.reachFrom(a, self.gfC.get(c), g, base, reads)) { self.gfMemo.set(base + f, 1); return true; }
            c = self.gfCNext.get(c);
        }
        return false;
    }

    // The per-function tables, made once the first question is asked.
    gfReady &self inout a:Ast -> void {
        if (self.gfState.len() > 0) { return; }
        for i in 0..a.fns.len() {
            self.gfState.push(false); self.gfWHead.push(-1); self.gfCHead.push(-1); self.gfRHead.push(-1);
        }
    }

    // Whether `f`'s own body writes the part `g` of its global by name (or, with `reads`, names
    // it at all): the record that does, a write's index into `gfW` or a read's into `gfR`, or -1.
    // `touchedRead` says which table the answer indexes.
    touchesHere &self inout a:Ast f:long g:GPlace reads:bool -> long {
        self.gfReady(a);
        self.gfInfo(a, f);
        self.touchedRead = false;
        w: long = self.gfWHead.get(f);
        while (w >= 0) {
            if (self.gfW.get(w) == g.root && self.gwOverlaps(w, g)) { return w; }
            w = self.gfWNext.get(w);
        }
        if (!reads) { return -1; }
        r: long = self.gfRHead.get(f);
        while (r >= 0) {
            if (self.gfR.get(r) == g.root && self.fieldsOverlap(self.gfRFirst.get(r), self.gfRCount.get(r), g)) {
                self.touchedRead = true;
                return r;
            }
            r = self.gfRNext.get(r);
        }
        return -1;
    }

    // The function, `f` or one it reaches, that touches the part `g` as `reachesBy` found, for
    // the message; the record that does is left in `touchedAt` (and `touchedRead`). A walk of its
    // own, done once per refusal.
    toucherFrom &self inout a:Ast f:long g:GPlace reads:bool inout seen:HashMap<long, bool> -> long {
        if (f < 0) {
            at: long = self.fanOut(a, f);
            for k in 0..self.gfFanN.getOr(f, 0) {
                t: long = self.toucherFrom(a, self.gfFan.get(at + k), g, reads, seen);
                if (t >= 0) { return t; }
            }
            return -1;
        }
        if (seen.has(f)) { return -1; }
        seen.put(f, true);
        at: long = self.touchesHere(a, f, g, reads);
        if (at >= 0) { self.touchedAt = at; self.touchPath.clear(); self.touchPath.push(f); return f; }
        c: long = self.gfCHead.get(f);
        while (c >= 0) {
            t: long = self.toucherFrom(a, self.gfC.get(c), g, reads, seen);
            if (t >= 0) { self.touchPath.push(f); return t; }
            c = self.gfCNext.get(c);
        }
        return -1;
    }

    // Write `w` reaches the part `g` of its global when one's fields lead to the other's: all of a
    // global is above every field of it, and `gReg.items` is not below `gReg.count`.
    gwOverlaps &self w:long g:GPlace -> bool { return self.fieldsOverlap(self.gfWFirst.get(w), self.gfWCount.get(w), g); }
    // The fields at `first` (`count` of them, in `gfWFields`) against the part `g`.
    fieldsOverlap &self first:long count:long g:GPlace -> bool {
        n: long = count;
        if (g.count < n) { n = g.count; }
        for k in 0..n { if (self.gfWFields.get(first + k) != self.gpFields.get(g.first + k)) { return false; } }
        return true;
    }

    // The part of a global `path` (a global and the steps below it, as `holdPath` gives them)
    // names, its fields kept in `gpFields`.
    placeOfPath &self path:Vec<Sym> -> GPlace {
        out: GPlace = GPlace { key: NO_SYM, root: NO_SYM, first: self.gpFields.len(), count: 0 };
        if (path.len() == 0) { return out; }
        out.root = path.get(0);
        out.key = out.root;
        out.count = fieldSteps(path);
        if (out.count == 0) { return out; }
        s: String;
        s.pushStr(nameOf(out.root));
        for k in 1..out.count + 1 {
            self.gpFields.push(path.get(k));
            s.push('.');
            s.pushStr(nameOf(path.get(k)));
        }
        out.key = internString(s);
        return out;
    }

    // The functions whose address the program takes, by index.
    ensureAddressed &self inout a:Ast -> void {
        if (self.gfAddrDone) { return; }
        self.gfAddrDone = true;
        seen: HashMap<str, bool>;
        for j in 0..gAddressedFns.len() {
            n: Sym = gAddressedFns.get(j);
            if (seen.has(nameOf(n))) { continue; }
            seen.put(nameOf(n), true);
            sig: Sym = NO_SYM;
            if (j < gAddressedSigs.len()) { sig = gAddressedSigs.get(j); }
            hit: Option<long> = self.fnAt.find(n as long);
            match hit { Some(fi) { self.gfAddr.push(fi); self.gfAddrSig.push(sig); } None { } }
        }
    }
    // Whether the addressed function at `k` may be what a call along edge `e` reaches: -1 is any
    // fn value, and an edge below it a fn value of one type (`fnValueEdge`), which holds only a
    // function that fits it (`fnSigsFit`, which the checker holds every fn value to). A function
    // addressed at no type is the float formatter a float's `any` box carries as a word
    // (`lower.k` `boxAny`), which only `fmt.k`'s cast of that word reads back: no typed fn value
    // holds it, and `fanOut` adds it where a raw word may be called.
    addrFits &self k:long e:long -> bool {
        if (e == -1) { return true; }
        sig: Sym = self.gfAddrSig.get(k);
        if (sig == NO_SYM) { return false; }
        return fnSigsFit((0 - 2 - e) as Sym, sig);
    }

    // The functions a call along edge `e` (below 0) may reach, as a run of `gfFan` from where this
    // answers, `gfFanN` long; worked out once per edge. A fn value reaches the addressed functions
    // its type fits (`addrFits`). One of a type some `unsafe` code makes of a raw word
    // (`gRawFnSigs`: `fmt.k`'s `callDisplay` reads a vtable slot and calls it) may also hold any
    // function the compiler placed in a vtable, which no `&f` names: every implementation whose
    // shape fits (`rawFits`). Edge -1, a fn value whose type is not known (a dependency's), reaches
    // both kinds, all of them.
    fanOut &self inout a:Ast e:long -> long {
        hit: Option<long> = self.gfFanAt.find(e);
        match hit { Some(at) { return at; } None { } }
        self.ensureAddressed(a);
        self.ensureVtab(a);
        at: long = self.gfFan.len();
        seen: HashMap<long, bool>;
        for k in 0..self.gfAddr.len() {
            fi: long = self.gfAddr.get(k);
            if (self.addrFits(k, e) && !seen.has(fi)) { seen.put(fi, true); self.gfFan.push(fi); }
        }
        raw: bool = e == -1;
        if (!raw) { for s in gRawFnSigs { if (fnSigsFit((0 - 2 - e) as Sym, s)) { raw = true; } } }
        if (raw) {
            for k in 0..self.gfAddr.len() {
                fi: long = self.gfAddr.get(k);
                if (self.gfAddrSig.get(k) == NO_SYM && !seen.has(fi)) { seen.put(fi, true); self.gfFan.push(fi); }
            }
            for fi in self.gfVtab {
                if (seen.has(fi)) { continue; }
                if (e == -1 || rawFits(a, (0 - 2 - e) as Sym, fi)) { seen.put(fi, true); self.gfFan.push(fi); }
            }
        }
        self.gfFanAt.put(e, at);
        self.gfFanN.put(e, self.gfFan.len() - at);
        return at;
    }

    // Every function the compiler places in a vtable: each method of each implementation.
    ensureVtab &self inout a:Ast -> void {
        if (self.gfVtabDone) { return; }
        self.gfVtabDone = true;
        seen: HashMap<long, bool>;
        for i in 0..gReg.implCount() {
            im: TraitImplDef = gReg.implAt(i);
            ti: long = gReg.findTraitSym(im.trait.name);
            if (ti < 0) { continue; }
            t: TraitDef = gReg.traitDef(ti);
            for k in 0..t.methodCount {
                hit: Option<long> = self.fnAt.find((implMethodName(im, gReg.traitMethodAt(t, k).name)) as long);
                match hit { Some(fi) { if (!seen.has(fi)) { seen.put(fi, true); self.gfVtab.push(fi); } } None { } }
            }
        }
    }

    // Reads function `f`'s body once, for the `var` globals it writes by name and what it calls.
    // A dependency's function names no global of this package (it cannot include it), but it can
    // call back into this package's code through a fn value it was handed or a trait object's
    // method. Its own compile recorded which (`DepFact`s with a negative parameter, from
    // `scanExpr`), and those become its callees here: any addressed function, or any
    // implementation of that slot.
    gfInfo &self inout a:Ast f:long -> void {
        if (self.gfState.get(f)) { return; }
        self.gfState.set(f, true);
        fn: FnNode = a.fns.get(f);
        if (isExternFn(f)) {
            wasF: long = self.gfCur;
            self.gfCur = f;
            fi: long = fnFactOf(f);
            if (fi < 0) { self.gwEdge(-1); }
            else {
                fact: FnFact = gFacts.fns.get(fi);
                for k in 0..fact.depCount {
                    d: DepFact = gFacts.depAt(fact, k);
                    if (d.param == CB_FNVALUE) { self.gwEdge(-1); }
                    if (d.param == CB_DISPATCH) {
                        ts: Vec<long> = self.slotTargets(d.trait, d.slot);
                        for t in ts { self.gwEdge(t); }
                    }
                }
            }
            self.gfCur = wasF;
            return;
        }
        if (fn.isTemplate || fn.body < 0 || isUnchecked(f)) { return; }
        // The borrow locals of the function being held, put back after: this runs in the middle
        // of holding one.
        saved: HashMap<long, NodeId> = map![];
        swapValues(&saved, &self.alias);
        wasCur: long = self.gfCur;
        self.gfCur = f;
        self.gwBlock(a, fn.body);
        self.gfCur = wasCur;
        swapValues(&saved, &self.alias);
    }

    // `place` written: the part of a `var` global it names, down to its first step that is not a
    // field (`gReg.items[i].n` writes `gReg.items`).
    gwMark &self inout a:Ast place:NodeId -> void {
        path: Vec<Sym>;
        if (!self.holdPath(a, place, NO_SYM, &path) || path.len() == 0) { return; }
        if (!isVarGlobalName(path.get(0))) { return; }
        n: long = fieldSteps(path);
        path.truncate(n + 1);
        self.gwRecord(path);
    }
    // All of the global `place` is rooted at: what an `asm` block is handed may be an address
    // it reaches anything from.
    gwMarkWhole &self inout a:Ast place:NodeId -> void {
        path: Vec<Sym>;
        if (!self.holdPath(a, place, NO_SYM, &path) || path.len() == 0) { return; }
        self.gwMarkName(a, path.get(0));
    }
    // Argument `k` of call `c`, whose callee writes through it: where the callee writes it, field
    // by field (`calleePaths`), below the part of a global the argument names. `gReg.bump()` with
    // `bump` writing `self.count` writes `gReg.count`.
    gwMarkCall &self inout a:Ast c:CallNode k:long arg:NodeId -> void {
        path: Vec<Sym>;
        if (!self.holdPath(a, arg, NO_SYM, &path) || path.len() == 0) { return; }
        if (!isVarGlobalName(path.get(0))) { return; }
        n: long = fieldSteps(path);
        if (n + 1 < path.len()) { path.truncate(n + 1); self.gwRecord(path); return; }
        qs: Vec<Sym> = self.calleePaths(a, c, k);
        for q in qs {
            fs: Vec<Sym>;
            fs.extend(path);
            appendFields(&fs, nameOf(q));
            self.gwRecord(fs);
        }
    }
    gwMarkName &self inout a:Ast n:Sym -> void {
        if (!isVarGlobalName(n)) { return; }
        whole: Vec<Sym>;
        whole.push(n);
        self.gwRecord(whole);
    }
    // A write of the global `path` starts with, at the fields after it.
    gwRecord &self path:Vec<Sym> -> void {
        self.gfW.push(path.get(0));
        self.gfWFirst.push(self.gfWFields.len());
        self.gfWCount.push(path.len() - 1);
        for k in 1..path.len() { self.gfWFields.push(path.get(k)); }
        self.gfWNext.push(self.gfWHead.get(self.gfCur));
        self.gfWHead.set(self.gfCur, self.gfW.len() - 1);
    }
    // Whether `id` is a place rooted at a `var` global.
    namesVarGlobal &self inout a:Ast id:NodeId -> bool {
        r: Sym = self.holdRoot(a, id);
        return r != NO_SYM && isVarGlobalName(r);
    }
    // The steps under a place `grMark` already named: what they compute (an index, a call yielding
    // a borrow) is read for itself, but the place is not named again by its root.
    gwSpine &self inout a:Ast id:NodeId -> void {
        if (id == NO_NODE) { return; }
        e: Expr = a.expr(id);
        if (e.op == Op.Lvalue) { return; }
        if (e.op == Op.FunctionCall || e.op == Op.MethodCall) { self.gwExpr(a, id); return; }
        match e.payload {
            Sub(v) { self.gwSpine(a, v); }
            Field(i) { self.gwSpine(a, a.fields.get(i).base); }
            Index(i) {
                ix: IndexNode = a.indexes.get(i);
                self.gwSpine(a, ix.base);
                self.gwExpr(a, ix.index);
                self.gwExpr(a, ix.sliceStart); self.gwExpr(a, ix.sliceEnd);
            }
            _ { self.gwExpr(a, id); }
        }
    }
    // The part of a `var` global `place` names, read or written by name: the place cut at its
    // first step that is not a field, as a write's is.
    grMark &self inout a:Ast place:NodeId -> void {
        if (!self.namesVarGlobal(a, place)) { return; }
        path: Vec<Sym>;
        if (!self.holdPath(a, place, NO_SYM, &path) || path.len() == 0) { return; }
        if (!isVarGlobalName(path.get(0))) { return; }
        path.truncate(fieldSteps(path) + 1);
        self.gfR.push(path.get(0));
        self.gfRFirst.push(self.gfWFields.len());
        self.gfRCount.push(path.len() - 1);
        for k in 1..path.len() { self.gfWFields.push(path.get(k)); }
        self.gfRNext.push(self.gfRHead.get(self.gfCur));
        self.gfRHead.set(self.gfCur, self.gfR.len() - 1);
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
                    if (pc.kind == AsmKind.In) { self.gwMarkWhole(a, pc.value); }
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
                if (!strWord(a, nodes.get(k)) && self.calleeWrites(a, c, k)) { self.gwMarkCall(a, c, k, nodes.get(k)); }
            }
            self.gwExpr(a, c.callee);
            if (c.slot == SLOT_FNPTR || c.callee != NO_NODE) { self.gwEdge(fnValueEdge(c)); return; }
            if (c.slot != NO_SLOT) {
                ts: Vec<long> = self.dispatchTargets(a, c);
                for t in ts { self.gwEdge(t); }
                return;
            }
            hit: Option<long> = self.fnAt.find(c.name as long);
            match hit { Some(fi) { self.gwEdge(fi); } None { } }
            return;
        }
        if (e.op == Op.Lvalue) { self.grMark(a, id); return; }
        p2: Payload = e.payload;
        match p2 {
            Sub(v)   { self.gwExpr(a, v); }
            Field(i) {
                // A place in a `var` global is named as the whole place (`gReg.count`), not as its
                // root, which would stand for all of the global.
                if (self.namesVarGlobal(a, id)) { self.grMark(a, id); self.gwSpine(a, a.fields.get(i).base); }
                else { self.gwExpr(a, a.fields.get(i).base); }
            }
            Index(i) {
                ix: IndexNode = a.indexes.get(i);
                if (self.namesVarGlobal(a, id)) { self.grMark(a, id); self.gwSpine(a, ix.base); }
                else { self.gwExpr(a, ix.base); }
                self.gwExpr(a, ix.index);
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

    // One function held to immutability and to what its loops lend, in the body of a `recover`:
    // every function's first error is reported, and the driver stops after the phase
    // (`stopIfErrors`).
    guardGuarded &self inout a:Ast at:long -> void {
        enterFn(a.fns.get(at).name);
        if (!canRecover()) { self.guardOne(a, at); return; }
        unsafe { recover { self.guardOne(a, at); } else { } }
    }
    guardOne &self inout a:Ast at:long -> void {
        self.hFn = at;                 // whose parameters `noteLend` asks about
        if (self.alias.len() > 0) { self.alias.clear(); }
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
            if (!f.isTemplate) { self.fnAt.put(f.name as long, i); }
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

    // Records what a dependent cannot see in this function: the code it may run that the
    // dependent's own program supplies. That is a call through a fn value (any function the
    // dependent addresses) or a dispatch (any implementation of that trait's slot), made here or
    // by something this calls. Each is recorded as a `DepFact` whose parameter says which
    // (`CB_FNVALUE`, `CB_DISPATCH`), and the dependent's guard follows them (`gfInfo`) to the
    // `var` globals they write.
    noteCallbacks &self inout a:Ast c:CallNode -> void {
        if (c.slot == SLOT_FNPTR || c.callee != NO_NODE) { self.addDep(CB_FNVALUE, intern("$fn"), 0, 0); return; }
        if (c.slot != NO_SLOT) { self.addDep(CB_DISPATCH, a.expr(c.receiver).structName, c.slot, 0); return; }
        hit: Option<long> = self.fnAt.find(c.name as long);
        g: long = -1;
        match hit { Some(i) { g = i; } None { return; } }
        if (isExternFn(g)) {
            fi: long = fnFactOf(g);
            if (fi < 0) { self.addDep(CB_FNVALUE, intern("$fn"), 0, 0); return; }
            fact: FnFact = gFacts.fns.get(fi);
            for k in 0..fact.depCount {
                d: DepFact = gFacts.depAt(fact, k);
                if (d.param < 0) { self.addDep(d.param, d.trait, d.slot, d.pos); }
            }
            return;
        }
        d: long = self.depHead.get(g);
        while (d >= 0) {
            dd: DepFact = self.deps.get(d);
            if (dd.param < 0) { self.addDep(dd.param, dd.trait, dd.slot, dd.pos); }
            d = self.depNext.get(d);
        }
    }

    // Parameter `r` of the function being scanned reaches position `pos` of call `c`: whatever
    // dispatches the callee hands that position to, this function hands `r` to.
    inheritDeps &self inout a:Ast c:CallNode pos:long r:long -> void {
        if (c.slot == SLOT_FNPTR || c.callee != NO_NODE) { return; }
        if (c.slot != NO_SLOT) {
            self.addDep(r, a.expr(c.receiver).structName, c.slot, pos);
            return;
        }
        hit: Option<long> = self.fnAt.find(c.name as long);
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
                if (d.param >= 0 && self.dispatchWritesTrait(a, d.trait, d.slot, d.pos)) { m = m | (1 << d.param); }
                k = k + 1;
            }
            if (m != self.writes.get(at)) { self.writes.set(at, m); self.changed = true; }
            return;
        }
        self.cur = at;
        f: FnNode = a.fns.get(at);
        if (self.paramIx.len() > 0) { self.paramIx.clear(); }
        if (self.alias.len() > 0) { self.alias.clear(); }
        for k in 0..f.argCount {
            p: VarDeclNode = a.paramAt(f, k);
            if (throughParam(p)) { self.paramIx.put(p.name as long, k); }
        }
        self.mask = self.writes.get(at);
        // In a package build every body is read, for the callbacks it makes (`noteCallbacks`).
        if ((!self.paramIx.isEmpty() && self.mask != WRITES_ALL) || gKlibMode) { self.scanBlock(a, f.body); }
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
        if (st.kind == StmtKind.While || st.kind == StmtKind.Recover) {
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
        hit: Option<long> = self.paramIx.find(n as long);
        match hit { Some(i) { self.mask = self.mask | (1 << i); } None { } }
    }

    scanExpr &self inout a:Ast id:NodeId -> void {
        if (id == NO_NODE) { return; }
        // A leaf (a name, a literal) writes nothing and has nothing under it, so it is recognized
        // in place, before the node is copied out. Most nodes are leaves, and this runs every round.
        lo: Op = a.exprs[id].op;
        if (lo == Op.Lvalue || lo == Op.Literal || lo == Op.StringLit) { return; }
        e: Expr = a.expr(id);
        if (e.op == Op.Assignment && (self.noteAlias(a, e) || (e.kind == Lit.Struct && self.copyStore.len() > 0 && self.noteCopy(a, id, e)))) { return; }
        if (e.op == Op.Assignment) {
            if (throughPointer(a, e.left) && !self.probing) { self.mask = WRITES_ALL; }
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
            if (gKlibMode && !self.probing) { self.noteCallbacks(a, c); }
            for k in 0..nodes.len() {
                r: long = -1;
                if (!strWord(a, nodes.get(k))) { r = self.rootParam(a, nodes.get(k)); }
                if (r >= 0 && (self.calleeWrites(a, c, k) || (self.probing && self.reachesLater(a, c, nodes.get(k))))) {
                    self.mask = self.mask | (1 << r);
                }
                if (r >= 0 && gKlibMode && !self.probing) { self.inheritDeps(a, c, k, r); }
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
        hit: Option<long> = self.fnAt.find(c.name as long);
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
        if (self.wpIx.len() > 0) { self.wpIx.clear(); }
        if (self.wpAlias.len() > 0) { self.wpAlias.clear(); }
        self.wpTarget = p;
        fn: FnNode = a.fns.get(f);
        if (self.writes.get(f) == WRITES_ALL || isExternFn(f) || isUnchecked(f)) { self.wpAdd(intern("")); return; }
        if ((self.writes.get(f) & (1 << p)) == 0) { return; }
        for k in 0..fn.argCount {
            pd: VarDeclNode = a.paramAt(fn, k);
            if (throughParam(pd)) { self.wpIx.put(pd.name as long, k); }
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
            if (self.wpAlias.len() > 0) { self.wpAlias.remove(d.name as long); }
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
        if (st.kind == StmtKind.While || st.kind == StmtKind.Recover) {
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
        hit: Option<long> = self.wpIx.find(n as long);
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
                match r.payload { Sub(v) { if (n != NO_SYM) { self.wpAlias.put(n as long, v); return; } } _ { } }
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
                    hit: Option<long> = self.wpIx.find(n as long);
                    match hit { Some(i) { return i; } None { } }
                    if (self.wpAlias.len() > 0) {
                        src: Option<NodeId> = self.wpAlias.find(n as long);
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
                    ih: Option<long> = self.wpIx.find(ix.name as long);
                    match ih { Some(k) { r = k; } None { } }
                }
                if (r >= 0) { self.ppCut = true; }
                return r;
            }
            _ { }
        }
        return -1;
    }

    // Whether the callee of `c` writes through its parameter at position `pos` (the receiver is
    // position 0). A callee that cannot be pinned down answers yes: a function value (unless the
    // argument crosses as a plain copy), or a dispatch some implementation of which writes.
    calleeWrites &self inout a:Ast c:CallNode pos:long -> bool {
        if (c.slot == SLOT_FNPTR || c.callee != NO_NODE) {
            if (!fnValueArgPlain(a, c, pos)) { return true; }
            // A lend the fn type says is read may still be written: `fn(&P)` is `fn(P)`, and a
            // function that writes through its borrow fits either.
            return self.fanWriter(a, fnValueEdge(c), pos) >= 0;
        }
        if (c.slot != NO_SLOT) { return self.dispatchWrites(a, c, pos); }
        hit: Option<long> = self.fnAt.find(c.name as long);
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
                ti: long = gReg.findTraitSym(im.trait.name);
                if (ti >= 0) {
                    t: TraitDef = gReg.traitDef(ti);
                    if (slot >= 0 && slot < t.methodCount) {
                        m: Sym = implMethodName(im, gReg.traitMethodAt(t, slot).name);
                        hit: Option<long> = self.fnAt.find(m as long);
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
        if (self.alias.len() > 0) { self.alias.remove(n as long); }
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
            Sub(v) { self.alias.put(n as long, v); return true; }
            _ { }
        }
        return false;
    }

    // A copy's store (`gCopyBinds`) while it may still become a borrow: a second name for its place,
    // as `noteAlias` takes a borrow's, so a write through the copy counts as a write of the place.
    // That is what it will be if anything writes through it, and nothing is if nothing does.
    noteCopy &self inout a:Ast id:NodeId e:Expr -> bool {
        if (e.kind != Lit.Struct || self.copyStore.len() == 0 || !self.copyStore.has(id as long)) { return false; }
        match a.expr(e.left).payload {
            Name(n) { self.alias.put(n as long, e.right); return true; }
            _ { }
        }
        return false;
    }

    // ─── the checker's copies, decided ──────────────────────────────────────

    // Whether call `c` may hand argument `arg` by its address to code this compile does not see:
    // a dispatch or a call through a fn value, in a program that is not whole (a package build,
    // `--lib`, `--use`). A dependent's implementation of the trait, or a function another object
    // addresses, may write through it, so a copy handed so is taken as written: it becomes the
    // borrow such a write needs to land.
    reachesLater &self inout a:Ast c:CallNode arg:NodeId -> bool {
        if (!gKlibMode && !self.openObject) { return false; }
        if (c.slot == NO_SLOT && c.callee == NO_NODE) { return false; }
        return lentArg(a, arg);
    }

    // Each copy the checker noted (`gCopyBinds`) that the code after it writes through becomes a
    // borrow of the payload or element where it lies, and so does the copy it is read out of (the
    // hidden local a `match self.f` or a destructure reads into, the binding a nested match is on),
    // so the write lands in the value it was bound from. Then it is held to what a borrow allows:
    // what the code after it does that the checker found a borrow could not, and the `&self` calls
    // and the `var` global it noted for it, judged with the rest. The masks were made with every
    // copy read as its place (`noteCopy`), which is what they are now for those that became
    // borrows, and the rest are written by nothing.
    promoteCopies &self inout a:Ast -> void {
        n: long = gCopyBinds.len();
        if (n == 0) { return; }
        made: Vec<bool>;
        for k in 0..n { made.push(false); }
        for k in 0..n {
            c: CopyBind = gCopyBinds.get(k);
            if (c.subject || made.get(k) || !self.writesCopy(a, c)) { continue; }
            j: long = k;
            while (j >= 0 && !made.get(j)) {
                made.set(j, true);
                j = gCopyBinds.get(j).parent;
            }
        }
        self.copyStore.clear();
        for k in 0..n {
            if (!made.get(k)) { continue; }
            c: CopyBind = gCopyBinds.get(k);
            if (c.viaRef) {
                // A borrow a call returned: the store holds it already, and the local is its pointer.
                d: VarDeclNode = a.decls.get(c.decl);
                d.kind = Lit.Ref;
                a.decls.set(c.decl, d);
                e: Expr = a.expr(c.store);
                e.kind = Lit.Ref;
                e.structName = d.structName;
                a.setExpr(c.store, e);
            } else { borrowRetype(a, c.decl, c.store); }
            // Its declaration on: its store, and what reads it (an arm, a match and its arms, the
            // names a destructure reads out of it, and what follows them).
            restampFrom(a, c.body, declIndex(a, c.body, c.decl), c.name);
        }
        // Each reported, as the checker would have, and the compile stops after the guard.
        for k in 0..n {
            c: CopyBind = gCopyBinds.get(k);
            if (!made.get(k) || c.conflict.len == 0) { continue; }
            gPos = c.conflictPos;
            enterFn(c.fnName);
            if (!canRecover()) { failStr(stringOf(c.conflict)); }
            unsafe { recover { failStr(stringOf(c.conflict)); } else { } }
        }
        // What was noted for a copy that stayed one does not apply.
        i: long = gSelfLends.len();
        while (i > 0) {
            i = i - 1;
            s: long = gSelfLends.get(i).copy;
            if (s >= 0 && !made.get(s)) { gSelfLends.removeAt(i); }
        }
        i = gHeldArms.len();
        while (i > 0) {
            i = i - 1;
            h: long = gHeldArms.at(i).copy;
            if (h >= 0 && !made.get(h)) { gHeldArms.removeAt(i); }
        }
        gCopyBinds.clear();
    }

    // Whether the code after binding `c.name` writes through it: the walk that makes the write masks
    // (`scanBlock`), over its block from its declaration on, with the binding standing as parameter
    // 0. A copy read out of it (a nested match's) is a second name for it, so a write through that
    // counts too.
    writesCopy &self inout a:Ast c:CopyBind -> bool {
        if (self.paramIx.len() > 0) { self.paramIx.clear(); }
        if (self.alias.len() > 0) { self.alias.clear(); }
        self.paramIx.put(c.name as long, 0);
        self.mask = 0;
        self.probing = true;
        from: long = declIndex(a, c.body, c.decl);
        if (from >= 0) { for k in from..a.blockLen(c.body) { self.scanStmt(a, a.stmtAt(c.body, k)); } }
        self.probing = false;
        self.paramIx.clear();
        if (self.alias.len() > 0) { self.alias.clear(); }
        return (self.mask & 1) != 0;
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
                    hit: Option<long> = self.paramIx.find(n as long);
                    match hit { Some(i) { return i; } None { } }
                    if (self.alias.len() > 0) {
                        src: Option<NodeId> = self.alias.find(n as long);
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
                ih: Option<long> = self.paramIx.find(ix.name as long);
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
        if (st.kind == StmtKind.While || st.kind == StmtKind.Recover) {
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
            if (c != NO_SYM) { refuse(c, "is assigned to here"); }
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
            ci: long = -1;
            match e.payload { Call(i) { c = a.calls.get(i); ci = i; } _ { } }
            nodes: Vec<NodeId>;
            if (c.receiver != NO_NODE) { nodes.push(c.receiver); }
            for k in 0..c.argCount { nodes.push(a.argAt(c, k)); }
            for k in 0..nodes.len() {
                self.guardExpr(a, nodes.get(k));
                g: Sym = NO_SYM;
                if (!strWord(a, nodes.get(k))) { g = self.rootConst(a, nodes.get(k)); }
                if (g != NO_SYM) { self.guardArgument(a, c, k, g); }
                if (ci >= 0) { self.noteLend(a, ci, k, nodes.get(k)); }
            }
            if (ci >= 0) { self.holdWrittenBorrows(a, c, nodes); }
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

    // The law of exclusivity for a plain borrow (`r:&T`) the callee writes through, as the write
    // masks decide (a field stored, a method that writes, the borrow lent on): it is held to the
    // law as an `inout` lend is, so no other argument of the call may reach the same place. The
    // checker holds `inout` lends to this at the call; this one needs the masks, which only the
    // guard has. A call through a fn value asks every function the value may hold, and a dispatch
    // every implementation.
    holdWrittenBorrows &self inout a:Ast c:CallNode nodes:Vec<NodeId> -> void {
        n: long = nodes.len();
        if (n < 2) { return; }
        self.holdAliasedLends(a, c, nodes);
        writer: Vec<long>;
        any: bool = false;
        for k in 0..n {
            w: long = self.borrowWriter(a, c, k);
            writer.push(w);
            if (w >= 0) { any = true; }
        }
        if (!any) { return; }
        paths: Vec<Vec<Sym>>;
        for k in 0..n {
            path: Vec<Sym>;
            if (!lentArg(a, nodes.get(k)) || !lawPath(a, nodes.get(k), &path)) { path.clear(); }
            paths.push(path);
        }
        for k in 0..n {
            w: long = writer.get(k);
            if (w < 0 || paths[k].len() == 0) { continue; }
            for j in 0..n {
                if (j == k || !lawOverlap(paths[k], paths[j])) { continue; }
                by: String;
                by.pushStr("`");
                by.pushStr(fnText(a.fns.get(w).name));
                by.pushStr("`");
                if (c.slot != NO_SLOT || c.callee != NO_NODE) { by.pushStr(", which the call may reach,"); }
                p: VarDeclNode = a.paramAt(a.fns.get(w), k);
                how: String = format("writes through its parameter `{}`, so that lend is exclusive, as an `inout` one is", spokenName(p.name));
                if (p.conv == Conv.Inout) { how = format("takes its parameter `{}` as `inout`", spokenName(p.name)); }
                failStr(format("cannot lend `{}` mutably while `{}` is also used in the call to `{}`\nnote: {} {}\nhelp: clone one of them, or restructure the call",
                               lawText(paths[k]), lawText(paths[j]), calledName(c), by, how));
            }
        }
    }

    // The law of exclusivity where an argument is a borrow local: a match binding through a borrow
    // (`p` of `match e { Pt(p) { ... } }`), a destructured element, a loop's element. Its name says
    // nothing of what it points into, so the checker's per-call law, which compares the names the
    // arguments are written with, takes `f(&p, e)` for two places; but `p` is part of `e`, and inside
    // `f` a write through the one would change what the other was promised would hold still, which
    // the optimizer trusts (`--no-restrict`). So each argument's place is followed through the borrow
    // locals to what it points into (`holdPath`), and an argument some function the call reaches
    // writes through (`inout`, a `&T` it writes, a `&self` method that writes `self`) may not
    // overlap another there. Pairs whose own paths overlap were the checker's or `holdWrittenBorrows`'
    // to refuse, and are left to them.
    holdAliasedLends &self inout a:Ast c:CallNode nodes:Vec<NodeId> -> void {
        if (self.alias.len() == 0) { return; }
        n: long = nodes.len();
        any: bool = false;
        for k in 0..n { if (self.aliasRooted(a, nodes.get(k))) { any = true; } }
        if (!any) { return; }
        held: Vec<Vec<Sym>>;
        own: Vec<Vec<Sym>>;
        for k in 0..n {
            hp: Vec<Sym>;
            lp: Vec<Sym>;
            if (lentArg(a, nodes.get(k))) {
                if (!self.holdPath(a, nodes.get(k), NO_SYM, &hp)) { hp.clear(); }
                if (!lawPath(a, nodes.get(k), &lp)) { lp.clear(); }
            }
            held.push(hp);
            own.push(lp);
        }
        for k in 0..n {
            if (held[k].len() == 0) { continue; }
            w: long = self.lendWriter(a, c, k);
            if (w < 0) { continue; }
            for j in 0..n {
                if (j == k || held[j].len() == 0 || !pathsOverlap(held[k], held[j])) { continue; }
                if (!self.aliasRooted(a, nodes.get(k)) && !self.aliasRooted(a, nodes.get(j))) { continue; }
                if (own[k].len() > 0 && own[j].len() > 0 && lawOverlap(own[k], own[j])) { continue; }
                via: long = k;
                if (!self.aliasRooted(a, nodes.get(k))) { via = j; }
                failStr(format("cannot lend `{}` mutably while `{}` is also used in the call to `{}`\nnote: `{}` is a borrow of `{}`, so the two overlap, and `{}` writes through its parameter\nhelp: clone one of them, or restructure the call",
                               argText(own[k], held[k]), argText(own[j], held[j]), calledName(c),
                               argText(own[via], held[via]), pathText(held[via]), fnText(a.fns.get(w).name)));
            }
        }
    }

    // Whether the place `id` names is reached through a borrow local (`alias`).
    aliasRooted &self inout a:Ast id:NodeId -> bool {
        cur: NodeId = id;
        while (cur != NO_NODE) {
            e: Expr = a.expr(cur);
            match e.payload {
                Name(x) { return e.op == Op.Lvalue && self.alias.has(x as long); }
                Sub(v) { cur = v; }
                Field(f) { cur = a.fields.get(f).base; }
                Index(i) { cur = a.indexes.get(i).base; }
                _ { return false; }
            }
        }
        return false;
    }

    // A function call `c` may run that writes through the argument at `pos` (the receiver is 0), or
    // -1: a written plain borrow or a dispatch's `inout` (`borrowWriter`), or a direct call's
    // `inout` parameter or `&self` receiver whose body writes it.
    lendWriter &self inout a:Ast c:CallNode pos:long -> long {
        w: long = self.borrowWriter(a, c, pos);
        if (w >= 0 || c.slot != NO_SLOT || c.callee != NO_NODE) { return w; }
        fi: long = self.calleeAt(a, c);
        if (fi < 0) { return -1; }
        at: long = self.paramPos(a, fi, pos);
        if (at < 0 || !self.writesThrough(a, fi, at)) { return -1; }
        return fi;
    }

    // The function that writes through the plain borrow (`r:&T`) the argument at `pos` of call `c`
    // is lent to (the receiver is 0), or -1 when none does. An `inout` parameter of a direct call is
    // the checker's to hold, and a copy is never written.
    borrowWriter &self inout a:Ast c:CallNode pos:long -> long {
        if (c.slot == SLOT_FNPTR || c.callee != NO_NODE) {
            if (!fnValueArgPlain(a, c, pos)) { return -1; }
            return self.fanWriter(a, fnValueEdge(c), pos);
        }
        if (c.slot != NO_SLOT) {
            // The checker never sees which function a dispatch reaches, so an `inout` argument
            // here (past the receiver) is held to the law here too.
            ts: Vec<long> = self.dispatchTargets(a, c);
            for t in ts {
                if (self.writesBorrow(a, t, pos) || (pos > 0 && inoutAt(a, t, pos))) { return t; }
            }
            return -1;
        }
        hit: Option<long> = self.fnAt.find(c.name as long);
        match hit { Some(i) { if (self.writesBorrow(a, i, pos)) { return i; } } None { } }
        return -1;
    }

    // A function a call along fn-value edge `e` may reach that writes through its parameter at
    // `pos`, or -1. Each function the value may hold (`fanOut`) is asked as a direct call asks its
    // one callee.
    fanWriter &self inout a:Ast e:long pos:long -> long {
        at: long = self.fanOut(a, e);
        for k in 0..self.gfFanN.getOr(e, 0) {
            fi: long = self.gfFan.get(at + k);
            if (self.writesBorrow(a, fi, pos)) { return fi; }
        }
        return -1;
    }

    // Whether function `fi` writes through its parameter at `pos`, that parameter being a plain
    // borrow (`r:&T`, not `inout`).
    writesBorrow &self inout a:Ast fi:long pos:long -> bool {
        f: FnNode = a.fns.get(fi);
        if (pos >= f.argCount) { return false; }
        p: VarDeclNode = a.paramAt(f, pos);
        if (p.kind != Lit.Ref || p.conv == Conv.Inout || p.isVariadic) { return false; }
        return self.writesThrough(a, fi, pos);
    }

    // Whether function `fi` writes the caller's value through its parameter at `pos`: one it is
    // reached through (`throughParam`) whose bit the write masks set.
    writesThrough &self inout a:Ast fi:long pos:long -> bool {
        f: FnNode = a.fns.get(fi);
        if (pos >= f.argCount || !throughParam(a.paramAt(f, pos))) { return false; }
        w: long = self.writes.get(fi);
        return w == WRITES_ALL || (w & (1 << pos)) != 0;
    }

    // A const, or part of one, as the argument at `pos` of a call: fine for a parameter the
    // callee only reads, and for a copy; refused for one it writes through, and for a move.
    guardArgument &self inout a:Ast c:CallNode pos:long g:Sym -> void {
        if (c.slot == SLOT_FNPTR || c.callee != NO_NODE) {
            // The callee is unknown, but what crosses can say enough: a scalar or a `str` arrives
            // as a copy of the value or of the view (a str's bytes are never written through
            // it), so no callee can write the const through it. The fn type's parameter is asked
            // when it has one, the argument's own type otherwise. A lend the type names (a struct,
            // a slice) is asked of every function the value may hold; a move, or an aggregate
            // with no type to say what crosses, stays refused.
            if (fnValueArgPlain(a, c, pos)) {
                w: long = self.fanWriter(a, fnValueEdge(c), pos);
                if (w < 0) { return; }
                refuseStr(g, format("is lent through a fn value to `{}`, which writes its parameter `{}`",
                                    fnText(a.fns.get(w).name), spokenName(a.paramAt(a.fns.get(w), pos).name)));
            }
            refuse(g, "is passed to a function value, whose callee cannot be checked");
        }
        if (c.slot != NO_SLOT) {
            if (self.dispatchWrites(a, c, pos)) { refuseStr(g, format("is handed to the trait method `{}`, and at least one implementation writes it", nameOf(c.name))); }
            return;
        }
        hit: Option<long> = self.fnAt.find(c.name as long);
        match hit {
            Some(i) {
                f: FnNode = a.fns.get(i);
                if (pos >= f.argCount) { return; }
                p: VarDeclNode = a.paramAt(f, pos);
                if (throughParam(p)) {
                    w: long = self.writes.get(i);
                    if (w == WRITES_ALL || (w & (1 << pos)) != 0) {
                        refuseStr(g, format("is handed to `{}`, which writes its parameter `{}`", nameOf(c.name), nameOf(p.name)));
                    }
                    return;
                }
                if (p.kind == Lit.Struct && p.conv == Conv.Sink && gReg.needsDrop(p.structName)) {
                    refuseStr(g, format("would be moved into `{}`, which takes it with `sink`", nameOf(c.name)));
                }
            }
            None { refuseStr(g, format("is handed to `{}`, whose body the compiler cannot see", nameOf(c.name))); }
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
                        src: Option<NodeId> = self.alias.find(n as long);
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
    // The loop reads `xs`'s buffer and length once, and `x` may be a borrow into the buffer
    // (`Checker.bmForLoop`), so `xs` must stay as it is while the body runs. The body may read
    // it, but may not assign to it, lend it with `&`, hand it to a callee that writes through
    // that parameter or takes it, or move it. Writing an element through `x` is what
    // `for x in &xs` is for; in the plain form a struct element is read-only, as a `read`
    // parameter is, and a scalar is the loop's own copy. This is the rule a match arm holding a
    // borrow lives by (`Checker.bmArmBlock`), enforced here because only here is it known which
    // callees write through which parameters: `xs.len()` reads, `xs.push(v)` writes. Like that
    // rule, it follows the places the body names. A callee that reaches the collection some other
    // way is caught only when the collection is a `var` global it writes by name (`hGlobal`), or
    // a parameter such a global was lent to (`holdLends`).

    holdFunction &self inout a:Ast at:long -> void {
        self.hFn = at;
        self.hParam = -1;
        body: long = a.fns.get(at).body;
        if (self.alias.len() > 0) { self.alias.clear(); }
        self.holdScan(a, body);
        self.hParam = -1;
        if (self.alias.len() > 0) { self.alias.clear(); }
    }

    // Parameter `n`'s position in function `f`, or -1.
    paramIndex &self inout a:Ast f:long n:Sym -> long {
        if (f < 0 || n == NO_SYM) { return -1; }
        fd: FnNode = a.fns.get(f);
        for k in 0..fd.argCount { if (a.paramAt(fd, k).name == n) { return k; } }
        return -1;
    }

    notePh &self f:long k:long kind:long call:long pos:long -> void {
        if (k < 0 || k >= 64) { return; }
        key: long = f * 64 + k;
        self.phKind.push(kind); self.phCall.push(call); self.phPos.push(pos);
        self.phNext.push(self.phHead.getOr(key, -1));
        self.phHead.put(key, self.phKind.len() - 1);
    }

    // Notes argument `k` (`arg`) of call `ci` in function `hFn` as the guard's walk meets it.
    // Rooted at one of the function's parameters, it hands that parameter on (kind 1); rooted at
    // a `var` global, it lends the global, which `holdLends` judges once every function is read.
    noteLend &self inout a:Ast ci:long k:long arg:NodeId -> void {
        if (self.hFn < 0) { return; }                      // a global's initializer
        ek: Lit = a.expr(arg).kind;
        walkable: bool = ek == Lit.Struct || ek == Lit.Ref || ek == Lit.Slice;
        // A trait object made of a global lends it too (its methods reach it through the view), and
        // so does `&` of one (an `inout` scalar's argument). Neither can be walked, so they are
        // held only to the law of exclusivity.
        lends: bool = walkable || ek == Lit.TraitObj || (a.expr(arg).op == Op.AddressOf && ek != Lit.Fn);
        if (!lends) { return; }   // a copy
        r: Sym = self.holdRoot(a, arg);
        if (r == NO_SYM) { return; }
        pk: long = self.paramIndex(a, self.hFn, r);
        if (pk >= 0) { if (walkable) { self.notePh(self.hFn, pk, 1, ci, k); } return; }
        if (isVarGlobalName(r)) {
            path: Vec<Sym>;
            if (!self.holdPath(a, arg, NO_SYM, &path) || path.len() == 0 || path.get(0) != r) { path.clear(); path.push(r); }
            pl: GPlace = self.placeOfPath(path);
            self.lendCall.push(ci); self.lendPos.push(k); self.lendG.push(pl);
            self.lendAt.push(gPos); self.lendFn.push(a.fns.get(self.hFn).name);
            self.lendWalkable.push(walkable);
        }
    }

    // The functions call `c` may run: its callee, every implementation a dispatch reaches, every
    // addressed function a fn value of the call's type may hold for a call through one.
    callTargets &self inout a:Ast c:CallNode -> Vec<long> {
        out: Vec<long>;
        if (c.slot == SLOT_FNPTR || c.callee != NO_NODE) {
            e: long = fnValueEdge(c);
            at: long = self.fanOut(a, e);
            for k in 0..self.gfFanN.getOr(e, 0) { out.push(self.gfFan.get(at + k)); }
            return out;
        }
        if (c.slot != NO_SLOT) { return self.dispatchTargets(a, c); }
        hit: Option<long> = self.fnAt.find(c.name as long);
        match hit { Some(fi) { out.push(fi); } None { } }
        return out;
    }

    // A `var` global lent to a parameter that some function walks while calling something that
    // writes the global by name. Nothing at the call shows the write (the global is lent
    // read-only, and the writer names it directly), and the walk holds the buffer it read at the
    // start. For example, `walk(gV)` with `walk xs:&Vec<long>` looping over `xs` while calling
    // `grow()`, which pushes to `gV`, would read the elements out of the block the push freed.
    // This is the rule for a loop over the global itself (`hGlobal`), carried through the
    // parameters the global is handed to.
    //
    // The same lend is held to the law of exclusivity across the call: while the global is lent,
    // nothing the call reaches may write it by name, nor, when it is lent `inout`, read it. Each
    // lend is judged in the body of a `recover`, so every refused one is reported.
    holdLends &self inout a:Ast -> void {
        for i in 0..self.lendCall.len() {
            if (!canRecover()) { self.holdLend(a, i); }
            else { unsafe { recover { self.holdLend(a, i); } else { } } }
        }
        self.lendCall.clear(); self.lendPos.clear(); self.lendG.clear(); self.lendAt.clear(); self.lendFn.clear(); self.lendWalkable.clear();
    }
    holdLend &self inout a:Ast i:long -> void {
        c: CallNode = a.calls.get(self.lendCall.get(i));
        g: GPlace = self.lendG.get(i);
        ts: Vec<long> = self.callTargets(a, c);
        for t in ts {
            if (!self.lendWalkable.get(i)) { break; }
            if (self.phMemo.getOr(phKey(g.key, t, self.lendPos.get(i)), 0) == 2) { continue; }   // asked before
            if (self.phWrites(a, t, self.lendPos.get(i), g)) {
                gPos = self.lendAt.get(i);
                enterFn(self.lendFn.get(i));
                failStr(format("cannot lend `{}` to `{}`, which walks it while calling something that writes it\nnote: the walk (a `for` over that parameter) reads the elements in place, and the write can move or release them\nhelp: pass a copy, or make the changes after the call",
                               lastComponentOf(nameOf(g.root)), calledName(c)));
            }
        }
        mode: long = self.lendMode(a, c, self.lendPos.get(i));
        if (mode == LEND_COPY) { return; }
        // A call to an `unsafe` function is made inside `unsafe` code, which vouches for what the
        // callee does with what it is lent (it may even keep it: io's `setStdout`).
        if (c.slot == NO_SLOT && c.callee == NO_NODE && ts.len() == 1 && a.fns.get(ts.get(0)).isUnsafe) { return; }
        for t in ts {
            hit: bool = false;
            if (mode == LEND_INOUT) { hit = self.reachesAccess(a, t, g); } else { hit = self.reachesWrite(a, t, g); }
            if (hit) { self.refuseLend(a, c, i, t, mode == LEND_INOUT); }
        }
    }

    // How call `c` holds its argument at `pos` (the receiver is 0): as a copy of its own, lent to
    // be read, or lent `inout` (to a parameter declared so, to one the callee writes through, or
    // as a trait object, whose methods may write it).
    lendMode &self inout a:Ast c:CallNode pos:long -> long {
        if (c.slot == SLOT_FNPTR || c.callee != NO_NODE) {
            si: long = gFnSigs.find(c.sigKey);
            if (si >= 0) {
                sig: FnSig = gFnSigs.sigAt(si);
                if (pos < sig.paramCount && gFnSigs.paramAt(sig, pos).conv == Conv.Sink) { return LEND_COPY; }
            }
            if (self.calleeWrites(a, c, pos)) { return LEND_INOUT; }
            return LEND_READ;
        }
        if (c.slot != NO_SLOT) {
            if (self.dispatchWrites(a, c, pos)) { return LEND_INOUT; }
            return LEND_READ;
        }
        hit: Option<long> = self.fnAt.find(c.name as long);
        match hit {
            Some(i) {
                f: FnNode = a.fns.get(i);
                at: long = pos;
                if (at >= f.argCount && f.argCount > 0 && a.paramAt(f, f.argCount - 1).isVariadic) { at = f.argCount - 1; }
                if (at >= f.argCount) { return LEND_INOUT; }
                p: VarDeclNode = a.paramAt(f, at);
                if (p.kind == Lit.TraitObj) { return LEND_INOUT; }
                // A raw address is no lend: what is done through it is `unsafe` code's to vouch for.
                if (p.kind == Lit.Ptr) { return LEND_COPY; }
                if (!throughParam(p)) { return LEND_COPY; }
                // A `&self` receiver is lent `inout` only to a method that writes `self`.
                if (p.conv == Conv.Inout && !(at == 0 && c.receiver != NO_NODE)) { return LEND_INOUT; }
                w: long = self.writes.get(i);
                if (w == WRITES_ALL || (w & (1 << at)) != 0) { return LEND_INOUT; }
                return LEND_READ;
            }
            None { }
        }
        return LEND_INOUT;    // no body to read
    }

    // Lend `i` (to call `c`) refused: `t`, one of the functions the call runs, reaches a write of
    // the part lent by name, or with `inout` a read of it. The message names the function that
    // touches it and the part it touches.
    refuseLend &self inout a:Ast c:CallNode i:long t:long exclusive:bool -> void {
        g: GPlace = self.lendG.get(i);
        seen: HashMap<long, bool>;
        tf: long = self.toucherFrom(a, t, g, exclusive, &seen);
        lent: str = placeText(g.root, self.gpFields, g.first, g.count);
        touched: str = lent;
        who: str = calledName(c);
        if (tf >= 0) {
            who = fnText(a.fns.get(tf).name);
            at: long = self.touchedAt;
            if (self.touchedRead) { touched = placeText(self.gfR.get(at), self.gfWFields, self.gfRFirst.get(at), shorter(self.gfRCount.get(at), atLeastOne(g.count))); }
            else { touched = placeText(self.gfW.get(at), self.gfWFields, self.gfWFirst.get(at), shorter(self.gfWCount.get(at), atLeastOne(g.count))); }
        }
        how: str = "writes";
        if (tf >= 0 && self.touchedRead) { how = "reads"; }
        reach: String = format("`{}` {} `{}`", who, how, touched);
        if (tf >= 0 && tf != t) {
            // The functions between the callee and the one that touches the global, outermost
            // first: `touchPath` runs from the toucher back up.
            via: String;
            n: long = self.touchPath.len();
            k: long = n - 2;
            while (k >= 1) {
                if (via.len > 0) { via.pushStr(", "); }
                if (n - 2 - k == 3) { via.pushStr("..."); k = 0; }
                else { via.push('`'); via.pushStr(fnText(a.fns.get(self.touchPath.get(k)).name)); via.push('`'); k = k - 1; }
            }
            if (via.len > 0) { reach = format("`{}` {} `{}`, and the call to `{}` reaches it through {}", who, how, touched, calledName(c), via); }
            else { reach = format("`{}` {} `{}`, and the call to `{}` reaches it", who, how, touched, calledName(c)); }
        }
        gPos = self.lendAt.get(i);
        enterFn(self.lendFn.get(i));
        if (exclusive) {
            failStr(format("cannot lend `{}` mutably to `{}`, which {} it by name while it is lent\nnote: {}\nnote: an `inout` lend is exclusive for the whole call, so nothing the call reaches may read or write what it lends by name\nhelp: reach it through the parameter instead of by name, or make the change after the call",
                           lent, calledName(c), how, reach));
        }
        failStr(format("cannot lend `{}` to `{}`, which writes it by name while it is borrowed\nnote: {}\nnote: a borrow is read where it lies for the whole call, so nothing the call reaches may write what it borrows by name\nhelp: pass a copy, or make the change after the call",
                       lent, calledName(c), reach));
    }

    // Does function `f`, while a loop walks its parameter `k` (or a callee it hands `k` on to
    // walks it), call something that writes `g` by name? A dependency's function is not read: it
    // is taken to hold every parameter while it calls whatever it calls back (`gfInfo`).
    phWrites &self inout a:Ast f:long k:long g:GPlace -> bool {
        self.phTouched.clear();
        self.phBusy = false;
        found: bool = self.phFrom(a, f, k, g);
        for t in self.phTouched {
            if (self.phMemo.getOr(t, 0) == 3) {
                if (found) { self.phMemo.remove(t); } else { self.phMemo.put(t, 2); }
            }
        }
        self.phTouched.clear();
        return found;
    }
    phFrom &self inout a:Ast f:long k:long g:GPlace -> bool {
        if (f < 0) { return false; }
        if (isExternFn(f)) { return self.reachesWrite(a, f, g); }
        key: long = phKey(g.key, f, k);
        m: long = self.phMemo.getOr(key, 0);
        if (m == 1) { return true; }
        if (m != 0) { return false; }
        self.phMemo.put(key, 3);
        self.phTouched.push(key);
        at: long = self.phHead.getOr(f * 64 + k, -1);
        while (at >= 0) {
            c: CallNode = a.calls.get(self.phCall.get(at));
            hit: bool = false;
            if (self.phKind.get(at) == 0) { hit = self.callWritesGlobal(a, c, g); }
            else {
                ts: Vec<long> = self.callTargets(a, c);
                for t in ts { if (!hit && self.phFrom(a, t, self.phPos.get(at), g)) { hit = true; } }
            }
            if (hit) { self.phMemo.put(key, 1); return true; }
            at = self.phNext.get(at);
        }
        return false;
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
            if (p != NO_SYM) { self.alias.put(p as long, e.right); }
            // `$forsK = xs.asSlice()`: a loop over a type viewed as a slice walks `xs`.
            v: Sym = forViewOf(a, e.left);
            if (v != NO_SYM) {
                r: Expr = a.expr(e.right);
                match r.payload {
                    Call(c) { if (a.calls.get(c).receiver != NO_NODE) { self.alias.put(v as long, a.calls.get(c).receiver); } }
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
        src: Option<NodeId> = self.alias.find(p as long);
        setup: NodeId = NO_NODE;
        match src { Some(s) { setup = s; } None { return; } }
        path: Vec<Sym>;
        xs: NodeId = forContainer(a, setup);
        // Through the slice an `AsSlice` type handed the loop, to the collection itself.
        vs: Sym = forViewOf(a, xs);
        if (vs != NO_SYM) {
            hit: Option<NodeId> = self.alias.find(vs as long);
            match hit { Some(r) { xs = r; } None { } }
        }
        if (!self.holdPath(a, xs, NO_SYM, &path)) { return; }
        shownXs: str = self.spoken(a, xs, "");
        // A slice is a read-only view unless it is an `inout` parameter (`checkSliceStore`), and
        // lending its elements to the loop is writing through it.
        if (forLends(p) && a.expr(xs).kind == Lit.Slice && !self.inoutParam(a, xs)) {
            failStr(format("cannot write through the slice `{}` in `for x in &{}`\nnote: a slice is a read-only view unless it is an `inout` parameter\nhelp: declare it `inout {}:[T]` and lend it with `&` at the call",
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
        if (isVarGlobalName(self.hPath.get(0))) {
            self.hGlobal = self.hPath.get(0);
            walked: Vec<Sym> = self.hPath.clone();
            self.hPlace = self.placeOfPath(walked);
        }
        // A parameter walked: what the body calls is recorded against it (`holdLends`).
        self.hParam = self.paramIndex(a, self.hFn, self.hPath.get(0));
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
        if (st.kind == StmtKind.While || st.kind == StmtKind.Recover) {
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
            // The assignments the desugaring writes are not writes of anything the loop holds: a
            // loop's own pointer, the slice an `AsSlice` loop views its collection through, and a
            // borrow local bound to its place. (`$forsK = xs.asSlice()` names `xs` only through
            // the alias `holdNote` just made; the call itself is judged below, by what `asSlice`
            // writes.)
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
            if (self.hParam >= 0) {
                match e.payload { Call(ci) { self.notePh(self.hFn, self.hParam, 0, ci, 0); } _ { } }
            }
            walked: GPlace = self.hPlace;
            if (self.hGlobal != NO_SYM && self.callWritesGlobal(a, c, walked)) {
                failStr(format("cannot change `{}` while `for {} in {}` walks it\nnote: `{}` is written by `{}`, which the loop body calls\nnote: the loop reads the elements in place, so nothing it calls may change the collection\nhelp: collect the changes and make them after the loop",
                               self.hShown, spokenName(self.hx), self.hShown, self.hShown, calledName(c)));
            }
            for k in 0..nodes.len() {
                if (self.holdCalleeWrites(a, c, k)) {
                    // Only the fields the callee writes count: `self.err()` bumping `self.errors`
                    // leaves alone the `self.cur.attrs` a loop walks. That is asked only where it
                    // can matter, for an argument that is a strict prefix of the walked path
                    // (`self` for `self.cur.attrs`); anything else is all or nothing.
                    how: str = keepString(format("handed to `{}`, which writes it", calledName(c)));
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
                failStr(format("cannot assign to `{}`, a borrow of an element of `{}`\nhelp: assign to its fields, or write the element by index",
                               spokenName(self.hx), self.hShown));
            }
            if (!self.hLend) {
                failStr(format("cannot change `{}`: an element of `for {} in {}` is read-only\nnote: it is {}\nhelp: write `for {} in &{}` to change the elements",
                               shown, spokenName(self.hx), self.hShown, how,
                               spokenName(self.hx), self.hShown));
            }
            return;
        }
        if (pathsOverlap(path, self.hPath)) {
            failStr(format("cannot change `{}` while `for {} in {}` walks it\nnote: it is {}\nnote: the loop reads the elements in place, so its body may not change the collection\nhelp: collect the changes and make them after the loop",
                           shown, spokenName(self.hx), self.hShown, how));
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
            failStr(format("cannot move `{}` while `for {} in {}` walks it\nnote: the loop reads the elements in place",
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
        hit: Option<long> = self.fnAt.find(c.name as long);
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

    // A place as the source spells it, for a message. This is `holdPath`'s walk, but following an
    // alias only through the compiler's own hidden locals (a loop's view `$forsK`, a match's
    // `$matchN`), so a binding the user named (`args` in `Call(args)`) is said by that name rather
    // than as the payload slot it borrows. `below` adds fields under it.
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
                src: Option<NodeId> = self.alias.find(n as long);
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

    // The variable `holdPath` would start its path at, without building the path: what the lend
    // walk asks of every argument.
    holdRoot &self inout a:Ast id:NodeId -> Sym {
        cur: NodeId = id;
        steps: long = 0;
        while (cur != NO_NODE && steps < 256) {
            steps = steps + 1;
            e: Expr = a.expr(cur);
            if (e.op == Op.Lvalue) {
                match e.payload {
                    Name(x) {
                        src: Option<NodeId> = self.alias.find(x as long);
                        match src { Some(s) { cur = s; continue; } None { } }
                        return x;
                    }
                    _ { return NO_SYM; }
                }
            }
            if (e.op == Op.FunctionCall || e.op == Op.MethodCall) {
                if (e.kind != Lit.Ref && e.kind != Lit.Ptr && e.kind != Lit.Slice) { return NO_SYM; }
                match e.payload {
                    Call(i) {
                        c: CallNode = a.calls.get(i);
                        r: Sym = self.holdRoot(a, c.receiver);
                        if (r != NO_SYM) { return r; }
                        for k in 0..c.argCount {
                            r = self.holdRoot(a, a.argAt(c, k));
                            if (r != NO_SYM) { return r; }
                        }
                    }
                    _ { }
                }
                return NO_SYM;
            }
            match e.payload {
                Sub(v) { cur = v; }
                Field(f) { cur = a.fields.get(f).base; }
                Index(i) {
                    ix: IndexNode = a.indexes.get(i);
                    if (ix.base == NO_NODE) { return ix.name; }
                    cur = ix.base;
                }
                _ { return NO_SYM; }
            }
        }
        return NO_SYM;
    }

    // The place an expression names, root first, through borrow locals and loop pointers to what
    // they point into. A field adds its name and an index adds `*` (any element); a call yielding
    // a borrow or a pointer gives the place of its receiver (or of its first argument that has
    // one) followed by `*`. `stop` (the loop's own `x`) is taken as it is, not followed. False
    // for anything that is not a place.
    holdPath &self inout a:Ast id:NodeId stop:Sym inout out:Vec<Sym> -> bool {
        if (id == NO_NODE) { return false; }
        e: Expr = a.expr(id);
        if (e.op == Op.Lvalue) {
            n: Sym = NO_SYM;
            match e.payload { Name(x) { n = x; } _ { return false; } }
            if (n != stop) {
                src: Option<NodeId> = self.alias.find(n as long);
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

// One (global, function, parameter) question of `phWrites`, as a number.
local phKey g:Sym f:long k:long -> long { return ((g as long) << 32) | (f * 64 + k); }

// A `var` global's name.
local isVarGlobalName n:Sym -> bool {
    gi: long = gReg.findGlobalSym(n);
    return gi >= 0 && gReg.globalDef(gi).isVar;
}

// Whether the argument at `pos` of a call through a fn value crosses as a copy or a lend rather
// than a move: a scalar, a `str` (a view whose bytes are never written), or a fn value. The fn
// type's parameter is asked when the call knows its signature, and the argument's own type
// otherwise. With the signature known, a struct or a slice the type lends, or gives as a copy,
// qualifies too: a fn value holds only a function whose parameters fit its type (`fnSigsFit`),
// no function that writes an `inout` parameter fits (`enforceFnRef`), a slice is written only
// through `inout`, and a `sink` of a type that owns nothing writes the callee's own copy. Only a
// `sink` of an owning type is more than that: a move. A struct lent this way may still be written
// by a function that takes it as a borrow (`fn(&P)` is `fn(P)`); `fanWriter` asks that.
local fnValueArgPlain inout a:Ast c:CallNode pos:long -> bool {
    k: Lit = Lit.Void;
    si: long = gFnSigs.find(c.sigKey);
    if (si >= 0) {
        sig: FnSig = gFnSigs.sigAt(si);
        if (pos < sig.paramCount) {
            fp: FnParam = gFnSigs.paramAt(sig, pos);
            k = fp.kind;
            if (k == Lit.Struct || k == Lit.Ref || k == Lit.Slice) {
                return fp.conv != Conv.Sink || !gReg.needsDrop(fp.name);
            }
        }
    }
    if (k == Lit.Void && pos < c.argCount) { k = a.expr(a.argAt(c, pos)).kind; }
    return isInteger(k) || k == Lit.Bool || k == Lit.Char || k == Lit.Float || k == Lit.Double
           || k == Lit.Str || k == Lit.Fn;
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

// An argument lent by address for the law of exclusivity: `&` of a place, a borrow, a struct, a
// trait object or a slice, as the checker's `noteAccess` counts one. A backed enum is not one,
// however typed: its value is its backing integer, copied into the call.
local lentArg inout a:Ast id:NodeId -> bool {
    e: Expr = a.expr(id);
    if (e.op == Op.AddressOf) { return e.kind != Lit.Fn; }
    if (e.kind == Lit.Struct && e.structName != NO_SYM) {
        named: str = nameOf(e.structName);
        if (gReg.isEnumType(named) && !gReg.isSumType(named)) { return false; }
    }
    return e.kind == Lit.Ref || e.kind == Lit.Struct || e.kind == Lit.TraitObj || e.kind == Lit.Slice;
}

// The place an argument names for the law of exclusivity, read as the checker's `pathOf` reads
// it: through `&`, a coercion to a trait object and a lent place's `*r`, then the root and its
// fields and elements, an element of a constant index as `[7]` and of any other as `[*]`. False
// for an rvalue, which lives in a temporary of its own and aliases nothing.
local lawPath inout a:Ast id:NodeId inout out:Vec<Sym> -> bool {
    rev: Vec<Sym>;
    cur: NodeId = id;
    while (cur != NO_NODE) {
        e: Expr = a.expr(cur);
        p: Payload = e.payload;
        if (e.op == Op.AddressOf || e.op == Op.MakeTraitObj || lentPlaceOf(a, cur) != NO_NODE) {
            inner: NodeId = NO_NODE;
            match p { Sub(v) { inner = v; } _ { } }
            if (inner == NO_NODE) { return false; }
            cur = inner;
            continue;
        }
        done: bool = false;
        match p {
            Name(x) {
                if (e.op != Op.Lvalue) { return false; }
                rev.push(x);
                done = true;
            }
            Field(f) {
                fd: FieldNode = a.fields.get(f);
                rev.push(fd.name);
                cur = fd.base;
            }
            Index(i) {
                ix: IndexNode = a.indexes.get(i);
                rev.push(lawIndex(a, ix.index));
                if (ix.base == NO_NODE) { rev.push(ix.name); done = true; }
                else { cur = ix.base; }
            }
            _ { return false; }
        }
        if (done) {
            k: long = rev.len();
            while (k > 0) { k = k - 1; out.push(rev.get(k)); }
            return true;
        }
    }
    return false;
}

local lawIndex inout a:Ast id:NodeId -> Sym {
    if (id != NO_NODE) {
        e: Expr = a.expr(id);
        if (e.op == Op.Literal) {
            match e.payload { Num(v) { return internString(format("[{}]", v)); } _ { } }
        }
    }
    return intern("[*]");
}

// Two places overlap unless some step of both is provably apart: distinct roots, distinct field
// names, or two distinct constant indices. One a prefix of the other reaches all of it.
local lawOverlap p:Vec<Sym> q:Vec<Sym> -> bool {
    if (p.len() == 0 || q.len() == 0) { return false; }
    n: long = p.len();
    if (q.len() < n) { n = q.len(); }
    for k in 0..n {
        x: Sym = p.get(k);
        y: Sym = q.get(k);
        if (x == y) { continue; }
        xi: bool = strStartsWith(nameOf(x), "[");
        yi: bool = strStartsWith(nameOf(y), "[");
        if (!(xi && yi && (nameOf(x) == "[*]" || nameOf(y) == "[*]"))) { return false; }
    }
    return true;
}

// A place as the checker's message spells it: `v`, `p.l`, `xs[*]`.
local lawText p:Vec<Sym> -> str {
    s: String;
    for k in 0..p.len() {
        c: str = nameOf(p.get(k));
        if (k == 0) { s.pushStr(spokenName(p.get(k))); continue; }
        if (k > 0 && !strStartsWith(c, "[")) { s.push('.'); }
        s.pushStr(c);
    }
    return keepString(s);
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

// Whether an assignment target reaches its place through a raw pointer (a dereference, or an
// index on a pointer, a `str` or a slice), which may point at anything at all.
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
// write `unsafe` smuggles past this guard does). Without this, `putStr(w, HEX[d..d+1])` would be
// refused, because `putStr` hands `s.ptr` to `Write.write`. A slice's `.ptr` still counts, since
// a slice's elements are writable.
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
    gi: long = gReg.findGlobalSym(n);
    if (gi < 0) { return false; }
    return !gReg.globalDef(gi).isVar;
}
// The refusal for a write to an immutable global. `why` is a fragment that follows "it" in the
// note ("is assigned to here", "is lent with `&`, which allows writing it").
local refuse g:Sym why:str -> void {
    failStr(format("cannot write to immutable global `{}`\nnote: it {}\nhelp: declare it `var {}: ...` if it is meant to change", lastComponentOf(nameOf(g)), why, lastComponentOf(nameOf(g))));
}
local refuseStr g:Sym why:String -> void { unsafe { refuse(g, why.view()); } }

// A part of a global as the source spells it: `gReg.items`.
local placeText root:Sym fields:Vec<Sym> first:long count:long -> str {
    s: String;
    s.pushStr(lastComponentOf(nameOf(root)));
    for k in 0..count { s.push('.'); s.pushStr(nameOf(fields.get(first + k))); }
    return keepString(s);
}

// A touched part is shown down to the lent part's depth, or one field when all of a global is
// lent: what a callee writes deeper (a `Vec`'s own `buf.cap`) says nothing to the reader.
local shorter x:long y:long -> long { if (x < y) { return x; } return y; }
local atLeastOne n:long -> long { if (n < 1) { return 1; } return n; }

// A function as a message names it: a method as `T.method`, with the type left qualified for the
// message's own spelling to render; anything else by its bare name.
local fnText n:Sym -> str {
    full: str = nameOf(n);
    i: long = full.len - 1;
    while (i > 0) {
        if (charAt(full, i) == '_') {
            head: str = strSlice(full, 0, i);
            if (gReg.findStruct(head) >= 0 || gReg.findEnum(head) >= 0) {
                return keepString(format("{}.{}", head, lastMethodOf(full)));
            }
        }
        i = i - 1;
    }
    return lastComponentOf(full);
}
// What follows the last `_` of a method's name: the method itself.
local lastMethodOf s:str -> str {
    k: long = s.len - 1;
    while (k > 0 && charAt(s, k) != '_') { k = k - 1; }
    return strSlice(s, k + 1, s.len - k - 1);
}

// The edge a call through a fn value makes (`gwEdge`): below -1, standing for the addressed
// functions a fn value of the call's type may hold; -1, any of them, when the type is not known.
local fnValueEdge c:CallNode -> long {
    if (c.sigKey == NO_SYM) { return -1; }
    return 0 - 2 - (c.sigKey as long);
}

// Whether function `fi` may be what a call through a fn value of type `sig` reaches when the value
// was made of a raw word (`fanOut`): the same number of parameters, each of the type the fn type
// says, but that a word (an integer or a pointer) may stand for any parameter passed as an
// address (a borrow, a struct, a pair), which is how a vtable's receiver arrives; and the same
// kind of result.
local rawFits inout a:Ast sig:Sym fi:long -> bool {
    si: long = gFnSigs.find(sig);
    if (si < 0) { return true; }
    s: FnSig = gFnSigs.sigAt(si);
    f: FnNode = a.fns.get(fi);
    if (s.paramCount != f.argCount) { return false; }
    for k in 0..s.paramCount {
        p: FnParam = gFnSigs.paramAt(s, k);
        q: VarDeclNode = a.paramAt(f, k);
        if (p.kind == Lit.TypeVar || q.kind == Lit.TypeVar) { continue; }
        if (p.kind == q.kind && (p.name == q.structName || p.name == NO_SYM || q.structName == NO_SYM)) { continue; }
        if (rawWord(p.kind) && (byAddress(q.kind) || rawWord(q.kind))) { continue; }
        return false;
    }
    if (s.ret.base == f.returnKind) { return true; }
    return rawWord(s.ret.base) && rawWord(f.returnKind);
}
local rawWord k:Lit -> bool { return k == Lit.Ptr || k == Lit.Long || k == Lit.U64; }
local byAddress k:Lit -> bool {
    return k == Lit.Ref || k == Lit.Struct || k == Lit.Tuple || k == Lit.Str || k == Lit.Slice || k == Lit.TraitObj;
}

// Whether function `fi`'s parameter at `pos` is declared or inferred `inout`.
local inoutAt inout a:Ast fi:long pos:long -> bool {
    f: FnNode = a.fns.get(fi);
    if (pos >= f.argCount) { return false; }
    p: VarDeclNode = a.paramAt(f, pos);
    return p.kind == Lit.Ref && p.conv == Conv.Inout && !p.isVariadic;
}

// An argument as a message names it: as written (`lawPath`), or, for one that is no place of its
// own (a borrow a call returned), the place it points into (`holdPath`).
local argText own:Vec<Sym> held:Vec<Sym> -> str {
    if (own.len() > 0) { return lawText(own); }
    return pathText(held);
}
