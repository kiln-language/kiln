// The facts table: what a package's own compile decided about it, which its dependents would
// otherwise have to re-derive from bodies they do not check.
//
// Per source function: its parameters' final conventions and representations (a read-only
// struct parameter is a borrow, which is the call ABI), its return type as settled (a closure
// written without `-> T`), whether it never returns, which by-reference parameters it writes
// through, and the trait dispatches it hands a parameter to (whose answer depends on every
// implementation in the final program, so a dependent re-asks it). Per global: what the
// evaluator folded it to, as bytes with their pointers named, so a dependent's compile-time code
// can read it. And the globals a startup initializer of this package (or one below it) may write,
// which a dependent's fold must not trust.
//
// A function's facts are found by its index in the tree (`fnFactOf`): a `.klib` lists them per
// module, in the order of the module's function nodes, and the reader files each under the index
// that node got (`1-cumulation/KlibTree.k`). A global's are found by its qualified name, which is
// unique and which the evaluator asks by. The encoding is the `.klib`'s; this is only the table.
#include <support::compiler>
#include <parse::{ast, registry}>
#include <stdlib::{chars, map, option, string, vec}>

// A `&self` method called, in a `match` arm through a borrow, on the place whose payload the arm
// holds. The checker notes it (`bmArmArg`); the guard refuses it only if the method writes `self`
// (`ConstGuard.holdSelfLends`), which its write masks decide once every body is settled.
// `callee` is the method's function, `pos` where the call stands, `what` the place, `made` the
// binding the arm holds. `copy` is -1, or the binding in `gCopyBinds` the arm holds only if the
// guard makes it a borrow, and then the call is refused only if it does. `destr`: the borrow is a
// destructured name, not a match binding, for the words.
pub struct SelfLend { callee: long, pos: long, fnName: Sym, what: str, made: Sym, copy: long, destr: bool }
pub var gSelfLends: Vec<SelfLend>;

// A binding of a payload that owns nothing, in a `match` through a borrow (of an `inout` or `&T`
// parameter, a `&self`, a borrow local, a global, a field reached through one of those, or
// `match &x`), and a name a destructure through a borrow binds to an element that owns nothing
// (`a, b = self.pair`). Such a binding is a borrow of the payload or element where it lies when the
// code after it writes through it (assigns a field, lends it mutably, calls a method that writes
// `self` on it), so the write lands in the value it came from, and a copy when it is only read.
// Which methods write is for the guard's write masks to say, so the checker notes each binding here
// and the guard decides (`ConstGuard.promoteCopies`). So is the hidden local a `match self.f` or a
// destructure reads its subject into: it has to become a borrow of the place too once a binding of
// it does. Until the guard decides, its walk takes the binding's store as a second name for the
// place (`copyStore`), so the masks already count a write through the binding as a write of what it
// was bound from.
// `decl` and `store` are the local's declaration and its store, and `body` the block both stand in:
// what follows the declaration there is where the local is used (an arm, the rest of a block).
// `subject` says it is a hidden local, made a borrow only with a binding read out of it, and
// `viaRef` that its place is a borrow a call returned (`v.at(i)`), which the store holds already.
// `parent` is
// the copy it is read out of (a hidden subject, or the binding a nested match is on), or -1;
// `conflict` the first thing the code after it does that a borrow does not allow (what
// `Checker.bmArmBlock` refuses), said where it stands, `conflictPos`.
pub struct CopyBind { name: Sym, decl: long, store: NodeId, body: long, subject: bool, viaRef: bool, parent: long,
                      fnName: Sym, conflict: str, conflictPos: long }
pub var gCopyBinds: Vec<CopyBind>;

// ─── walking a body ──────────────────────────────────────────────────────────

// The expressions a statement evaluates itself (not those of the blocks it holds).
pub stmtExprs inout a:Ast st:Stmt -> Vec<NodeId> {
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

// The blocks a statement holds, for a walk that only looks for something in them.
pub childBlocks inout a:Ast st:Stmt -> Vec<long> {
    out: Vec<long>;
    if (st.kind == StmtKind.If) {
        at: long = st.at;
        while (at >= 0) { br: IfNode = a.ifs.get(at); out.push(br.body); at = br.elseIf; }
    } else if (st.kind == StmtKind.While || st.kind == StmtKind.Recover) {
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

// ─── a local made a borrow ───────────────────────────────────────────────────
// The checker makes a match binding, a destructured element, a loop's element and a read parameter
// borrows; the guard makes the copies above borrows once it knows they are written through. Both
// rewrite the tree the same way.

// `v: T; v = <place>;` made `v: &T; v = &<place>;`. The uses of `v` follow by `restampBlock`.
pub borrowRetype inout a:Ast declAt:long asn:NodeId -> void {
    d: VarDeclNode = a.decls.get(declAt);
    d.kind = Lit.Ref;
    a.decls.set(declAt, d);
    e: Expr = a.expr(asn);
    e.right = a.leafOf(Op.AddressOf, Payload.Sub(e.right), Lit.Ref, d.structName);
    e.kind = Lit.Ref;
    e.structName = d.structName;
    a.setExpr(asn, e);
}

// Where declaration `decl` stands in block `b`, or -1. Found when asked, not kept: the ownership
// pass adds statements to a block (in place), which moves those after them.
pub declIndex inout a:Ast b:long decl:long -> long {
    if (b < 0) { return -1; }
    for k in 0..a.blockLen(b) {
        st: Stmt = a.stmtAt(b, k);
        if (st.kind == StmtKind.VarDecl && st.at == decl) { return k; }
    }
    return -1;
}

// Every mention of `n` read as the borrow it now is: a name typed as the struct becomes the `Ref`,
// or half the body would read a struct where its slot holds a pointer. Statements `from` onward of
// block `b` (a name declared at `from` is used only after it).
pub restampFrom inout a:Ast b:long from:long n:Sym -> void {
    for k in from..a.blockLen(b) { restampStmt(a, a.stmtAt(b, k), n); }
}

pub restampBlock inout a:Ast b:long n:Sym -> void {
    for k in 0..a.blockLen(b) { restampStmt(a, a.stmtAt(b, k), n); }
}

pub restampStmt inout a:Ast st:Stmt n:Sym -> void {
    if (st.kind == StmtKind.VarDecl) { restampExpr(a, a.decls.get(st.at).init, n); return; }
    if (st.kind == StmtKind.Expr || st.kind == StmtKind.Call) {
        restampExpr(a, a.exprStmts.get(st.at).value, n);
        return;
    }
    if (st.kind == StmtKind.Return) { restampExpr(a, a.returns.get(st.at).value, n); return; }
    if (st.kind == StmtKind.If) {
        c: long = st.at;
        while (c >= 0) {
            nd: IfNode = a.ifs.get(c);
            restampExpr(a, nd.cond, n);
            restampBlock(a, nd.body, n);
            c = nd.elseIf;
        }
        return;
    }
    if (st.kind == StmtKind.While || st.kind == StmtKind.Recover) {
        w: WhileNode = a.whiles.get(st.at);
        restampExpr(a, w.cond, n);
        restampBlock(a, w.body, n);
        if (w.step >= 0) { restampBlock(a, w.step, n); }
        return;
    }
    if (st.kind == StmtKind.Loop || st.kind == StmtKind.Unsafe || st.kind == StmtKind.Block) {
        restampBlock(a, a.blockStmts.get(st.at).body, n);
        return;
    }
    if (st.kind == StmtKind.With) { restampBlock(a, a.withs.get(st.at).body, n); return; }
    if (st.kind == StmtKind.Match) {
        m: MatchNode = a.matches.get(st.at);
        for k in 0..m.armCount {
            arm: ArmNode = a.arms.get(m.firstArm + k);
            restampExpr(a, arm.test, n);
            restampBlock(a, arm.body, n);
        }
        return;
    }
    if (st.kind == StmtKind.Asm) {
        nd: AsmNode = a.asms.get(st.at);
        for k in 0..nd.pieceCount {
            restampExpr(a, a.asmPieces.get(nd.firstPiece + k).value, n);
        }
        return;
    }
    if (st.kind == StmtKind.Destructure) {
        restampExpr(a, a.destructures.get(st.at).value, n);
        return;
    }
}

pub restampExpr inout a:Ast id:NodeId n:Sym -> void {
    if (id == NO_NODE) { return; }
    e: Expr = a.expr(id);
    p: Payload = e.payload;
    match p {
        Name(x) {
            if (e.op == Op.Lvalue && x == n && e.kind == Lit.Struct) {
                renamed: Expr = e;
                renamed.kind = Lit.Ref;
                a.setExpr(id, renamed);
            }
        }
        Sub(v)   { restampExpr(a, v, n); }
        Field(f) { restampExpr(a, a.fields.get(f).base, n); }
        Index(i) {
            ix: IndexNode = a.indexes.get(i);
            restampExpr(a, ix.base, n);
            restampExpr(a, ix.index, n);
            restampExpr(a, ix.sliceStart, n);
            restampExpr(a, ix.sliceEnd, n);
        }
        Call(c) {
            cn: CallNode = a.calls.get(c);
            restampExpr(a, cn.receiver, n);
            restampExpr(a, cn.callee, n);
            for k in 0..cn.argCount { restampExpr(a, a.argAt(cn, k), n); }
        }
        Lit(l) {
            ln: LitNode = a.lits.get(l);
            restampExpr(a, ln.rest, n);
            for k in 0..ln.initCount {
                restampExpr(a, a.inits.get(ln.firstInit + k).value, n);
            }
        }
        _ { }
    }
    restampExpr(a, e.left, n);
    restampExpr(a, e.right, n);
}

// The functions that never return, by name, as the settled program decided (`checkReturns`): the
// lowerer marks a call to one `noReturn`, so the back end knows no path leaves it.
pub var gNoReturnFns: HashMap<str, bool> = map![];

// A `match` arm holding a borrow into a `var` global's payload (`match &G.f { Some(r) { ... } }`).
// The checker refuses a write to the global the arm itself makes; one a function the arm calls
// makes, by naming the global, is the guard's to find (`ConstGuard.holdArms`), once it knows what
// every function writes. `body` is the arm's block, `pos` where the match stands, `path` the
// place it borrows into (the global, then fields; `*` where a step is not a field). `copy` is as a
// `SelfLend`'s: -1, or the binding in `gCopyBinds` the arm holds only if the guard makes it a borrow.
pub struct HeldArm { body: long, global: Sym, pos: long, fnName: Sym, made: Sym, path: Vec<Sym>, copy: long, destr: bool }
pub var gHeldArms: Vec<HeldArm>;

// Every function whose address the checked code takes (`&f`): what a call through a fn value may
// reach, for the guard's question of which globals such a call writes.
pub var gAddressedFns: Vec<Sym>;
// And the fn type each was addressed as, in step with it (NO_SYM where the type is not known): a
// call through a fn value reaches only the addressed functions that fit its type.
pub var gAddressedSigs: Vec<Sym>;
// The fn types some `unsafe` code makes of a raw word (`x as fn(..)`): a call through a fn value of
// one of them may reach any function the compiler placed in a vtable whose type it fits.
pub var gRawFnSigs: Vec<Sym>;
// Per function (by its index in the tree), the guard's mask of the parameters it writes through,
// itself or by what it calls (bit 62: through a raw pointer or `asm`, so all of them): what the
// lowerer records of a call's arguments (`callConventionsOf`).
pub var gFnWrites: Vec<long>;

pub struct ParamFact { conv: Conv, kind: Lit }
// `param` of the function is handed, through calls, to position `pos` of a dispatch through
// `trait`'s method `slot`.
pub struct DepFact { param: long, trait: Sym, slot: long, pos: long }
pub struct FnFact {
    divergent: bool,
    writes: long,                    // the guard's mask: bit k = writes through parameter k
    retKind: Lit, retStruct: Sym,
    firstParam: long, paramCount: long,
    firstDep: long, depCount: long
}
// What a global folded to: nothing (it initializes at startup), zero bytes (no initializer), a
// scalar, or an image.
pub enum GlobalState: int { Startup, Zero, Scalar, Image }
pub struct GlobalFact { name: Sym, state: GlobalState, value: long, image: long }
pub struct ImgFact { firstByte: long, byteCount: long, firstReloc: long, relocCount: long, isBlock: bool }
// A relocation inside an image. `image` indexes this table (a block); `concrete`/`trait` say
// which vtable a Vtable relocation names, which its label alone cannot be split back into.
pub struct RelocFact { offset: long, kind: RelocKind, target: Sym, image: long, delta: long,
                       concrete: Sym, trait: Sym }

pub struct Facts {
    fns: Vec<FnFact>,
    params: Vec<ParamFact>,
    deps: Vec<DepFact>,
    globals: Vec<GlobalFact>,
    globalAt: HashMap<str, long>,
    images: Vec<ImgFact>,
    bytes: Vec<u8>,
    relocs: Vec<RelocFact>,
    poisonAll: bool,
    poison: Vec<Sym>,
    poisonAt: HashMap<str, bool>
}

methods Facts for Default {
    new -> Facts {
        return Facts { fns: vec![], params: vec![], deps: vec![],
                       globals: vec![], globalAt: map![], images: vec![], bytes: vec![],
                       relocs: vec![], poisonAll: false, poison: vec![], poisonAt: map![] };
    }
}

// Everything the dependencies' `.klib`s said, merged: what a compile reads.
pub var gFacts: Facts;
// What this package's compile decided about itself: what it writes.
pub var gOutFacts: Facts;

// Per function of the tree, by its index: its facts in `gFacts`, or -1 (a function this compile
// owns, or one its package recorded nothing for). Filled as a `.klib`'s modules are loaded.
pub var gFnFact: Vec<long> = vec![];
// Writing: per function of the tree, its facts in `gOutFacts`, or -1.
pub var gOutFnFactAt: Vec<long> = vec![];

pub fnFactOf i:long -> long {
    if (i < 0 || i >= gFnFact.len()) { return -1; }
    return gFnFact.get(i);
}
pub noteFnFact i:long fact:long -> void {
    while (gFnFact.len() <= i) { gFnFact.push(-1); }
    gFnFact.set(i, fact);
}

// ─── instance functions other packages compiled ──────────────────────────────

// One instance function (a method of `Vec<long>`, `vecOf<long>`) a loaded `.klib` compiled and
// exports: its name, the alias it is linked by, what it was compiled against (the fingerprint,
// `Mono.fingerprint`), its facts in `gFacts`, and which `.klib` (`gKlibRank` orders them).
// Chained by name, in load order.
pub struct InstExport { name: Sym, alias: Sym, fp: long, fact: long, klib: long, next: long }
pub var gInstExports: Vec<InstExport> = vec![];
pub var gInstExportAt: HashMap<str, long> = map![];
// Per loaded `.klib`, its place in dependency order (each after what it depends on).
pub var gKlibRank: Vec<long> = vec![];

pub addInstExport e:InstExport -> void {
    at: long = gInstExports.len();
    gInstExports.push(e);
    head: long = gInstExportAt.getOr(nameOf(e.name), -1);
    if (head < 0) { gInstExportAt.put(nameOf(e.name), at); return; }
    while (gInstExports.get(head).next >= 0) { head = gInstExports.get(head).next; }
    prev: InstExport = gInstExports.get(head);
    prev.next = at;
    gInstExports.set(head, prev);
}

// The export a dependent links `name` to: of the `.klib`s that compiled it against what this
// compile sees (`fp`), the first in dependency order. -1 when there is none, and it is stamped here.
pub instExportFor name:Sym fp:long -> long {
    best: long = -1;
    i: long = gInstExportAt.getOr(nameOf(name), -1);
    while (i >= 0) {
        e: InstExport = gInstExports.get(i);
        if (e.fp == fp && (best < 0 || klibRank(e.klib) < klibRank(gInstExports.get(best).klib))) { best = i; }
        i = e.next;
    }
    return best;
}
local klibRank k:long -> long {
    if (k < 0 || k >= gKlibRank.len()) { return k; }
    return gKlibRank.get(k);
}

// Writing: this package's own instance functions, by name, to their facts in `gOutFacts`.
pub var gOutInstFact: HashMap<str, long> = map![];

// The label of a vtable an image points at, back to the pair it was made from. Filled where the
// evaluator promotes a trait object, read where the facts are written.
pub var gVtablePairs: HashMap<str, long> = map![];
pub var gVtableConcrete: Vec<Sym> = vec![];
pub var gVtableTrait: Vec<Sym> = vec![];

pub noteVtablePair label:str concrete:Sym trait:Sym -> void {
    if (gVtablePairs.has(label)) { return; }
    gVtablePairs.put(label, gVtableConcrete.len());
    gVtableConcrete.push(concrete);
    gVtableTrait.push(trait);
}

// A cursor over a metadata text (its methods are at the end of this file).
pub struct MetaIn { text: str, pos: long, failed: bool, why: String }

methods Facts {
    globalFact &self name:Sym -> long {
        hit: Option<long> = self.globalAt.find(nameOf(name));
        match hit { Some(i) { return i; } None { } }
        return -1;
    }
    paramAt &self f:FnFact k:long -> ParamFact { return self.params.get(f.firstParam + k); }
    depAt &self f:FnFact k:long -> DepFact { return self.deps.get(f.firstDep + k); }

    // Answers the new entry's index.
    addFn &self f:FnFact ps:Vec<ParamFact> ds:Vec<DepFact> -> long {
        first: long = self.params.len();
        self.params.extend(ps);
        firstDep: long = self.deps.len();
        self.deps.extend(ds);
        self.fns.push(FnFact { divergent: f.divergent, writes: f.writes,
                               retKind: f.retKind, retStruct: f.retStruct,
                               firstParam: first, paramCount: ps.len(),
                               firstDep: firstDep, depCount: ds.len() });
        return self.fns.len() - 1;
    }
    addGlobal &self g:GlobalFact -> void {
        self.globalAt.put(nameOf(g.name), self.globals.len());
        self.globals.push(g);
    }
    addPoison &self g:Sym -> void {
        if (self.poisonAt.has(nameOf(g))) { return; }
        self.poisonAt.put(nameOf(g), true);
        self.poison.push(g);
    }
}

// ─── the header's text ───────────────────────────────────────────────────────

// A name as `<length>:<bytes>`, or `-` for none: a name may hold anything a signature's spelling
// or a string literal does, spaces included, and this way nothing has to be escaped.
pub putName inout s:String n:Sym -> void {
    if (n == NO_SYM) { s.push('-'); return; }
    putText(s, nameOf(n));
}
pub putText inout s:String t:str -> void {
    s.pushLong(t.len);
    s.push(':');
    s.pushStr(t);
}


// A cursor over a metadata text. A malformed record is kept as what was expected and where, like a
// `Decoder`'s error: after the first, every read answers nothing and the cursor stays put, and the
// reader asks `ok` once it is done. The input was written by a compiler, so a mismatch means a
// damaged file; whoever reads one decides what that costs (`Klib.KlibCheck`).

pub metaIn text:str -> MetaIn {
    return MetaIn { text: text, pos: 0, failed: false, why: stringOf("") };
}

methods MetaIn {
    ok &self -> bool { return !self.failed; }
    atEnd &self -> bool {
        self.skipBlank();
        return self.failed || self.pos >= self.text.len;
    }
    skipBlank &self -> void {
        while (self.pos < self.text.len) {
            c: long = charAt(self.text, self.pos);
            if (c != ' ' && c != '\n') { return; }
            self.pos = self.pos + 1;
        }
    }
    word &self -> str {
        if (self.failed) { return ""; }
        self.skipBlank();
        start: long = self.pos;
        while (self.pos < self.text.len) {
            c: long = charAt(self.text, self.pos);
            if (c == ' ' || c == '\n') { return strSlice(self.text, start, self.pos - start); }
            self.pos = self.pos + 1;
        }
        return strSlice(self.text, start, self.pos - start);
    }
    num &self -> long {
        w: str = self.word();
        if (self.failed) { return 0; }
        got: Option<long> = parseLong(w);
        match got { Some(v) { return v; } None { } }
        self.bad(format("a number, found `{}`", w));
        return 0;
    }
    // `<length>:<bytes>` back to an interned name; `-` is none.
    name &self -> Sym {
        if (self.failed) { return NO_SYM; }
        self.skipBlank();
        // A prefixed name starts with its length, so a dash can only be the absence of one.
        if (charAt(self.text, self.pos) == '-') { self.pos = self.pos + 1; return NO_SYM; }
        t: str = self.text0();
        if (self.failed) { return NO_SYM; }
        return intern(t);
    }
    // `<length>:<bytes>` as text that lives as long as the metadata does.
    text0 &self -> str {
        if (self.failed) { return ""; }
        self.skipBlank();
        n: long = 0;
        while (self.pos < self.text.len && isDigit(charAt(self.text, self.pos))) {
            n = n * 10 + charAt(self.text, self.pos) - '0';
            self.pos = self.pos + 1;
        }
        if (charAt(self.text, self.pos) != ':' || self.pos + 1 + n > self.text.len) {
            self.bad(stringOf("a length-prefixed name"));
            return "";
        }
        self.pos = self.pos + 1;
        out: str = strSlice(self.text, self.pos, n);
        self.pos = self.pos + n;
        return out;
    }
    // The rest of the current line, without its newline.
    restOfLine &self -> str {
        if (self.failed) { return ""; }
        start: long = self.pos;
        while (self.pos < self.text.len && charAt(self.text, self.pos) != '\n') { self.pos = self.pos + 1; }
        out: str = strSlice(self.text, start, self.pos - start);
        if (self.pos < self.text.len) { self.pos = self.pos + 1; }
        return out;
    }
    // A blob: `n` raw bytes starting right after the current line's newline.
    blob &self n:long -> str {
        if (self.failed) { return ""; }
        if (self.pos < self.text.len && charAt(self.text, self.pos) == '\n') { self.pos = self.pos + 1; }
        if (n < 0 || self.pos + n > self.text.len) { self.bad(stringOf("a body running past the end")); return ""; }
        out: str = strSlice(self.text, self.pos, n);
        self.pos = self.pos + n;
        return out;
    }
    // The first malformed record, kept; the ones after it follow from it.
    bad &self what:String -> void {
        if (self.failed) { return; }
        self.failed = true;
        self.why = format("expected {} at byte {}", what, self.pos);
    }
}
