// A module's tree in a `.klib`: what its parser produced, already name-resolved, so a dependent
// neither lexes nor parses a dependency again.
//
// A module section is five chunks:
//
//     OPS       the module's registry operations, in parse order (`parse::regops`)
//     DECLS     a tree of its own: the module's top-level statements, every function node of the
//               module and its parameters, its globals' declarations (their initializers dropped:
//               a dependent never checks or runs them; what one folded to is in FACTS)
//     FACTS     per function of DECLS, in order, what checking it decided; per global its folded value
//     BODYIX    per function of DECLS, where its body is in BODIES (-1: none)
//     BODIES    one tree per function body, each addressable on its own
//
// A tree is dense and starts at zero in every arena; a reader shifts every index by where that
// arena starts in its own tree (`Rebase`), and a writer copies the nodes out of the program's
// tree to make one (`Graft`). Both walk a node through `parse::ast`'s `mapX`, which name each
// node type's index fields once. Bodies are snapshotted right after parsing: the checker rewrites
// a body in place, and the dependent checks one, when it has to, from the start.
#include <{Klib, Scanner, Module}>
#include <support::compiler>
#include <parse::{ast, astdump, parser, registry, regops, treecodec, upstream}>
#include <transform::facts>
#include <stdlib::{bytes, encode, map, mem, option, string, vec}>

// Marks a function node in DECLS whose body is in BODIES. Once loaded, it marks one whose body
// has not been read yet.
pub BODY_IN_CHUNK: long = BODY_LAZY;

// ─── writing: the graft ──────────────────────────────────────────────────────

// Copies nodes out of the program's tree into a dense one. `dst` is the tree being filled, and
// `side` the other: DECLS while a body is copied, the body while DECLS is. A function node always
// goes to DECLS, with its parameters, wherever it is met (a function declared inside a body), and
// its body is queued to be copied on its own. A node met twice in one chunk is copied once
// (`memo*`), so sharing in the parser's tree survives.
pub struct Graft {
    dst: Ast,
    side: Ast,
    inBody: bool,
    fnSrc: Vec<long>,       // per function of DECLS, its index in the program's tree
    queue: Vec<long>,       // functions of DECLS whose body is still to copy
    roots: Vec<long>,
    deferred: Vec<bool>,
    globals: Vec<Sym>,      // the module's globals, in order
    memoBase: Vec<long>,    // per arena, where its slots start in the two below
    memoIdx: Vec<long>,
    memoGen: Vec<long>,
    gen: long,
    shared: long            // nodes met more than once
}

pub graftOf src:Ast -> Graft {
    g: Graft = Graft { dst: Ast.new(), side: Ast.new(), inBody: false, fnSrc: vec![], queue: vec![],
                       roots: vec![], deferred: vec![], globals: vec![], memoBase: vec![],
                       memoIdx: vec![], memoGen: vec![], gen: 1, shared: 0 };
    total: long = 0;
    for k in 0..(Arena.Nowhere as long) + 1 {
        g.memoBase.push(total);
        total = total + memoLen(src, k as Arena);
    }
    g.memoIdx.reserve(total);
    g.memoGen.reserve(total);
    for k in 0..total { g.memoIdx.push(-1); g.memoGen.push(0); }
    return g;
}

// How many nodes of an arena can be met twice: the node arenas. Runs, names and the arenas a
// graft fills by hand (declarations, functions) are not memoized.
local memoLen src:Ast k:Arena -> long {
    match k {
        Exprs        { return src.exprs.len(); }
        Indexes      { return src.indexes.len(); }
        Calls        { return src.calls.len(); }
        Fields       { return src.fields.len(); }
        Lits         { return src.lits.len(); }
        Stmts        { return src.stmts.len(); }
        Blocks       { return src.blocks.len(); }
        Ifs          { return src.ifs.len(); }
        Whiles       { return src.whiles.len(); }
        Returns      { return src.returns.len(); }
        BlockStmts   { return src.blockStmts.len(); }
        Withs        { return src.withs.len(); }
        ExprStmts    { return src.exprStmts.len(); }
        Destructures { return src.destructures.len(); }
        Matches      { return src.matches.len(); }
        Asms         { return src.asms.len(); }
        _            { return 0; }
    }
}

// Every vector of a tree emptied, their storage kept for the next body.
pub clearAst inout a:Ast -> void {
    a.exprs.clear(); a.indexes.clear(); a.calls.clear(); a.fields.clear(); a.lits.clear();
    a.inits.clear(); a.args.clear(); a.stmts.clear(); a.stmtPos.clear(); a.blocks.clear(); a.stmtRuns.clear();
    a.ifs.clear(); a.whiles.clear(); a.returns.clear(); a.blockStmts.clear(); a.withs.clear();
    a.exprStmts.clear(); a.destructures.clear(); a.names.clear(); a.arms.clear(); a.matches.clear();
    a.asms.clear(); a.asmPieces.clear(); a.decls.clear(); a.params.clear(); a.fns.clear();
    a.structDecls.clear(); a.images.clear(); a.imageBytes.clear(); a.relocs.clear();
}

methods Graft {
    // DECLS as the tree being filled, or the body.
    toDecls &self -> void {
        if (!self.inBody) { return; }
        swapValues(&self.dst, &self.side);
        self.inBody = false;
    }
    toBody &self -> void {
        if (self.inBody) { return; }
        swapValues(&self.dst, &self.side);
        self.inBody = true;
    }

    memoGet &self arena:Arena v:long -> long {
        slot: long = self.memoBase.get(arena as long) + v;
        if (self.memoGen.get(slot) != self.gen) { return -1; }
        self.shared = self.shared + 1;
        return self.memoIdx.get(slot);
    }
    memoPut &self arena:Arena v:long at:long -> long {
        slot: long = self.memoBase.get(arena as long) + v;
        self.memoGen.set(slot, self.gen);
        self.memoIdx.set(slot, at);
        return at;
    }

    // A function node, into DECLS: its parameters with it, its body queued.
    copyFn &self src:Ast v:long -> long {
        was: bool = self.inBody;
        self.toDecls();
        f: FnNode = src.fns.get(v);
        ps: Vec<long>;
        for k in 0..f.argCount { ps.push(self.copyDecl(src, src.params.get(f.firstArg + k), false)); }
        first: long = self.dst.addParams(ps);
        body: long = f.body;
        if (body >= 0) { body = BODY_IN_CHUNK; }
        // A function with no bounds names none: what the parser left there is whichever block's came last.
        fb: long = f.firstBound;
        if (f.boundCount == 0) { fb = 0; }
        self.dst.fns.push(FnNode { name: f.name, returnKind: f.returnKind, returnStruct: f.returnStruct,
                                   visibility: f.visibility, file: f.file, pkg: f.pkg, isUnsafe: f.isUnsafe,
                                   isTemplate: f.isTemplate, firstBound: fb, boundCount: f.boundCount,
                                   firstArg: first, argCount: f.argCount, body: body, inferReturn: f.inferReturn,
                                   attrs: f.attrs });
        at: long = self.dst.fns.len() - 1;
        self.fnSrc.push(v);
        if (f.body >= 0) { self.queue.push(at); }
        if (was) { self.toBody(); }
        return at;
    }
    copyDecl &self src:Ast v:long dropInit:bool -> long {
        d: VarDeclNode = src.decls.get(v);
        if (dropInit) { d.init = NO_NODE; }
        y: VarDeclNode = mapDecl(d, self, src);
        self.dst.decls.push(y);
        return self.dst.decls.len() - 1;
    }

    // One top-level statement of the module, into DECLS.
    root &self src:Ast st:long deferred:bool -> void {
        s: Stmt = src.stmts.get(st);
        at: long = 0;
        if (s.kind == StmtKind.VarDecl) {
            // A global: its declaration without the initializer.
            self.globals.push(src.decls.get(s.at).name);
            d: long = self.copyDecl(src, s.at, true);
            at = self.dst.addStmt(StmtKind.VarDecl, d);
        } else {
            at = self.id(src, Arena.Stmts, st);
        }
        self.roots.push(at);
        self.deferred.push(deferred);
    }
}

methods Graft for IdMap {
    id &self src:Ast arena:Arena v:long -> long {
        if (v < 0 || arena == Arena.Bounds || arena == Arena.Nowhere) { return v; }
        if (arena == Arena.Fns) { return self.copyFn(src, v); }
        if (arena == Arena.Decls) { return self.copyDecl(src, v, false); }
        if (arena == Arena.StructDecls) {
            self.dst.structDecls.push(src.structDecls.get(v));
            return self.dst.structDecls.len() - 1;
        }
        hit: long = self.memoGet(arena, v);
        if (hit >= 0) { return hit; }
        match arena {
            Exprs {
                y: Expr = mapExpr(src.exprs.get(v), self, src);
                self.dst.exprs.push(y);
                return self.memoPut(arena, v, self.dst.exprs.len() - 1);
            }
            Stmts {
                y: Stmt = mapStmt(src.stmts.get(v), self, src);
                self.dst.stmts.push(y);
                self.dst.stmtPos.push(src.stmtPos.get(v));
                return self.memoPut(arena, v, self.dst.stmts.len() - 1);
            }
            Blocks {
                y: Block = mapBlock(src.blocks.get(v), self, src);
                self.dst.blocks.push(y);
                return self.memoPut(arena, v, self.dst.blocks.len() - 1);
            }
            Calls {
                y: CallNode = mapCall(src.calls.get(v), self, src);
                self.dst.calls.push(y);
                return self.memoPut(arena, v, self.dst.calls.len() - 1);
            }
            Fields {
                y: FieldNode = mapField(src.fields.get(v), self, src);
                self.dst.fields.push(y);
                return self.memoPut(arena, v, self.dst.fields.len() - 1);
            }
            ExprStmts {
                y: ExprStmtNode = mapExprStmt(src.exprStmts.get(v), self, src);
                self.dst.exprStmts.push(y);
                return self.memoPut(arena, v, self.dst.exprStmts.len() - 1);
            }
            Indexes {
                y: IndexNode = mapIndex(src.indexes.get(v), self, src);
                self.dst.indexes.push(y);
                return self.memoPut(arena, v, self.dst.indexes.len() - 1);
            }
            Lits {
                y: LitNode = mapLit(src.lits.get(v), self, src);
                self.dst.lits.push(y);
                return self.memoPut(arena, v, self.dst.lits.len() - 1);
            }
            Ifs {
                y: IfNode = mapIf(src.ifs.get(v), self, src);
                self.dst.ifs.push(y);
                return self.memoPut(arena, v, self.dst.ifs.len() - 1);
            }
            Whiles {
                y: WhileNode = mapWhile(src.whiles.get(v), self, src);
                self.dst.whiles.push(y);
                return self.memoPut(arena, v, self.dst.whiles.len() - 1);
            }
            Returns {
                y: ReturnNode = mapReturn(src.returns.get(v), self, src);
                self.dst.returns.push(y);
                return self.memoPut(arena, v, self.dst.returns.len() - 1);
            }
            BlockStmts {
                y: BlockStmtNode = mapBlockStmt(src.blockStmts.get(v), self, src);
                self.dst.blockStmts.push(y);
                return self.memoPut(arena, v, self.dst.blockStmts.len() - 1);
            }
            Withs {
                y: WithNode = mapWith(src.withs.get(v), self, src);
                self.dst.withs.push(y);
                return self.memoPut(arena, v, self.dst.withs.len() - 1);
            }
            Destructures {
                y: DestructureNode = mapDestructure(src.destructures.get(v), self, src);
                self.dst.destructures.push(y);
                return self.memoPut(arena, v, self.dst.destructures.len() - 1);
            }
            Matches {
                y: MatchNode = mapMatch(src.matches.get(v), self, src);
                self.dst.matches.push(y);
                return self.memoPut(arena, v, self.dst.matches.len() - 1);
            }
            Asms {
                y: AsmNode = mapAsm(src.asms.get(v), self, src);
                self.dst.asms.push(y);
                return self.memoPut(arena, v, self.dst.asms.len() - 1);
            }
            _ { }
        }
        failStr(format("internal compiler error: a graft asked for one element of a run ({})", arena as long));
        return v;
    }

    // A run is copied whole and appended in one piece, after its elements (which may append runs
    // of their own) are done.
    run &self src:Ast arena:Arena first:long count:long -> long {
        match arena {
            Args {
                ids: Vec<long>;
                for k in 0..count { ids.push(self.id(src, Arena.Exprs, src.args.get(first + k))); }
                return self.dst.addArgs(ids);
            }
            StmtRuns {
                ids: Vec<long>;
                for k in 0..count { ids.push(self.id(src, Arena.Stmts, src.stmtRuns.get(first + k))); }
                at: long = self.dst.stmtRuns.len();
                self.dst.stmtRuns.extend(ids);
                return at;
            }
            Params {
                ids: Vec<long>;
                for k in 0..count { ids.push(self.id(src, Arena.Decls, src.params.get(first + k))); }
                return self.dst.addParams(ids);
            }
            Inits {
                xs: Vec<InitNode>;
                for k in 0..count { xs.push(mapInit(src.inits.get(first + k), self, src)); }
                return self.dst.addInits(xs);
            }
            Names {
                at: long = self.dst.names.len();
                for k in 0..count { self.dst.names.push(src.names.get(first + k)); }
                return at;
            }
            Arms {
                xs: Vec<ArmNode>;
                for k in 0..count { xs.push(mapArm(src.arms.get(first + k), self, src)); }
                at: long = self.dst.arms.len();
                self.dst.arms.extend(xs);
                return at;
            }
            AsmPieces {
                xs: Vec<AsmPiece>;
                for k in 0..count { xs.push(mapAsmPiece(src.asmPieces.get(first + k), self, src)); }
                at: long = self.dst.asmPieces.len();
                self.dst.asmPieces.extend(xs);
                return at;
            }
            _ { }
        }
        failStr(format("internal compiler error: a graft asked for a run of a node arena ({})", arena as long));
        return first;
    }
}

// ─── the facts, per module ───────────────────────────────────────────────────

pub struct GlobalFactRec { name: Sym, state: GlobalState, value: long, image: long }
methods GlobalState for Decode {
    decode inp:&Decoder -> GlobalState {
        v: long = inp.getVarint();
        if (v < 0 || v > GlobalState.Image as long) { inp.fail("a global state no compiler writes"); v = 0; }
        return v as GlobalState;
    }
}

// ─── writing a package's modules ─────────────────────────────────────────────

// Per module of this package, right after parsing: where its DECLS and bodies are in the two
// buffers below, and its functions (each one's source index, and where its body chunk is).
pub struct OutModule { mod: long, declsAt: long, declsLen: long, bodiesAt: long, bodiesLen: long,
                       firstFn: long, fnCount: long, firstGlobal: long, globalCount: long }
pub var gOutModules: Vec<OutModule> = vec![];
pub var gOutDecls: Encoder;
pub var gOutBodies: Encoder;
pub var gOutFnSrc: Vec<long> = vec![];
pub var gOutBodyAt: Vec<long> = vec![];
pub var gOutBodyLen: Vec<long> = vec![];
pub var gOutGlobals: Vec<Sym> = vec![];
pub var gGraftShared: long = 0;

// Every module of this package, as its parser left it: the tree copied out (grafted) and written,
// before the checker rewrites a body.
pub snapshotModules inout p:Parser inout sc:Scanner -> void {
    g: Graft = graftOf(p.ast);
    for m in 0..sc.count() {
        if (sc.at(m).package == nameOf(gThisPkg)) {
            ids: Vec<long>;
            defs: Vec<bool>;
            for k in 0..p.pageIds.len() {
                if (p.pageMod.get(k) == m) { ids.push(p.pageIds.get(k)); defs.push(p.pageDeferred.get(k)); }
            }
            declsAt: long = gOutDecls.len();
            bodiesAt: long = gOutBodies.len();
            firstFn: long = gOutFnSrc.len();
            graftModule(&g, p.ast, ids, defs, &gOutDecls, &gOutBodies, &gOutBodyAt, &gOutBodyLen);
            gOutFnSrc.extend(g.fnSrc);
            firstGlobal: long = gOutGlobals.len();
            gOutGlobals.extend(g.globals);
            gOutModules.push(OutModule { mod: m, declsAt: declsAt, declsLen: gOutDecls.len() - declsAt,
                                         bodiesAt: bodiesAt, bodiesLen: gOutBodies.len() - bodiesAt,
                                         firstFn: firstFn, fnCount: g.fnSrc.len(),
                                         firstGlobal: firstGlobal, globalCount: g.globals.len() });
        }
    }
    gGraftShared = g.shared;
}

// Graft one module's top-level statements `ids` out of `src` (`defs` says, per statement, whether
// it is a macro read at the end of the page). DECLS is appended to `declsOut` and each body, as a
// tree of its own, to `bodiesOut`. For each function of DECLS, `bodyAt` gets where its body
// starts relative to where `bodiesOut` stood (-1 for none), and `bodyLen` how long it is.
pub graftModule inout g:Graft src:Ast ids:Vec<long> defs:Vec<bool> inout declsOut:Encoder
                inout bodiesOut:Encoder inout bodyAt:Vec<long> inout bodyLen:Vec<long> -> void {
    clearAst(&g.dst);
    clearAst(&g.side);
    g.inBody = false;
    g.fnSrc.clear(); g.queue.clear(); g.roots.clear(); g.deferred.clear(); g.globals.clear();
    g.gen = g.gen + 1;
    for k in 0..ids.len() { g.root(src, ids.get(k), defs.get(k)); }
    // The bodies, each a tree of its own. A body may hold a function declared inside it, whose
    // own body joins the queue.
    start: long = bodiesOut.len();
    at: Vec<long>;
    len: Vec<long>;
    q: long = 0;
    while (q < g.queue.len()) {
        fi: long = g.queue.get(q);
        q = q + 1;
        g.toBody();
        clearAst(&g.dst);
        g.gen = g.gen + 1;
        fsrc: FnNode = src.fns.get(g.fnSrc.get(fi));
        root: long = g.id(src, Arena.Blocks, fsrc.body);
        while (at.len() <= fi) { at.push(-1); len.push(0); }
        b: long = bodiesOut.len();
        encodeTree(&bodiesOut, g.dst);
        bodiesOut.putVarint(root);
        at.set(fi, b - start);
        len.set(fi, bodiesOut.len() - b);
        g.toDecls();
    }
    for k in 0..g.fnSrc.len() {
        if (k < at.len()) { bodyAt.push(at.get(k)); bodyLen.push(len.get(k)); }
        else { bodyAt.push(-1); bodyLen.push(0); }
    }
    encodeTree(&declsOut, g.dst);
    g.roots.encode(declsOut);
    g.deferred.encode(declsOut);
}

// ─── `--klib-verify` ─────────────────────────────────────────────────────────
// Every module of the package is written as it would be and read back in this process. Its
// top-level statements, dumped in `--emit=ast`'s form, must read as the parser's did, and the
// read-back tree, grafted again, must write the same bytes. Answers the number of modules that
// differ.

pub verifyKlibTrees inout p:Parser -> long {
    // The names come back through the table they were written to.
    ownSymsReadable();
    gSymInBase = gOwnSymBase;
    gSymInCount = gSymTable.len();
    bad: long = 0;
    nodes: long = 0;
    bytes: long = 0;
    for om in gOutModules {
        scratch: Ast;
        view: [u8] = "";
        unsafe { view = gOutDecls.view(); }
        d: Decoder;
        unsafe { d = decoderOf(view[om.declsAt..om.declsAt + om.declsLen]); }
        rb: Rebase = rebaseOf();
        rb.sameBounds = true;
        rb.startAt(scratch);
        decodeTree(&d, &scratch, &rb);
        roots: Vec<long> = decodeVec(&d);
        defs: Vec<bool> = decodeVec(&d);
        if (!d.done()) { bad = bad + 1; eprintln("  module {}: DECLS does not decode: {}", om.mod, d.error()); continue; }
        unsafe { view = gOutBodies.view(); }
        for f in 0..om.fnCount {
            at: long = gOutBodyAt.get(om.firstFn + f);
            if (at >= 0) {
                s: long = om.bodiesAt + at;
                bd: Decoder;
                unsafe { bd = decoderOf(view[s..s + gOutBodyLen.get(om.firstFn + f)]); }
                rb.startAt(scratch);
                decodeTree(&bd, &scratch, &rb);
                root: long = bd.getVarint() + rb.base.get(Arena.Blocks as long);
                if (!bd.done()) { bad = bad + 1; eprintln("  module {}: a body does not decode: {}", om.mod, bd.error()); }
                fn: FnNode = scratch.fns.get(f);
                fn.body = root;
                scratch.fns.set(f, fn);
            }
        }
        nodes = nodes + scratch.exprs.len() + scratch.stmts.len();
        bytes = bytes + om.declsLen + om.bodiesLen;
        // The dumps, statement by statement. A global's initializer is not carried, so the
        // parser's is set aside while its declaration is dumped.
        mine: Vec<long>;
        for k in 0..p.pageIds.len() { if (p.pageMod.get(k) == om.mod) { mine.push(p.pageIds.get(k)); } }
        if (mine.len() != roots.len()) { bad = bad + 1; eprintln("  module {}: {} statements, read back {}", om.mod, mine.len(), roots.len()); continue; }
        same: bool = true;
        for k in 0..mine.len() {
            st: Stmt = p.ast.stmts.get(mine.get(k));
            x: String;
            if (st.kind == StmtKind.VarDecl) {
                dv: VarDeclNode = p.ast.decls.get(st.at);
                was: NodeId = dv.init;
                dv.init = NO_NODE;
                p.ast.decls.set(st.at, dv);
                dumpStmt(p.ast, &x, st, 0);
                dv.init = was;
                p.ast.decls.set(st.at, dv);
            } else {
                dumpStmt(p.ast, &x, st, 0);
            }
            y: String;
            dumpStmt(scratch, &y, scratch.stmts.get(roots.get(k)), 0);
            if (!(x == y)) {
                same = false;
                unsafe { eprintln("  module {} statement {} differs:\n{}--- read back:\n{}", om.mod, k, x.view(), y.view()); }
                break;
            }
        }
        if (!same) { bad = bad + 1; continue; }
        // Written again from what was read: the same bytes.
        g2: Graft = graftOf(scratch);
        dOut: Encoder;
        bOut: Encoder;
        ats: Vec<long>;
        lens: Vec<long>;
        graftModule(&g2, scratch, roots, defs, &dOut, &bOut, &ats, &lens);
        unsafe {
            a1: [u8] = gOutDecls.view();
            b1: [u8] = gOutBodies.view();
            if (!bytesEqual(dOut.view(), a1[om.declsAt..om.declsAt + om.declsLen])
                || !bytesEqual(bOut.view(), b1[om.bodiesAt..om.bodiesAt + om.bodiesLen])) {
                bad = bad + 1;
                eprintln("  module {}: written again, the bytes differ ({}+{} against {}+{})", om.mod,
                         dOut.len(), bOut.len(), om.declsLen, om.bodiesLen);
            }
        }
    }
    eprintln("klib-verify: {} modules, {} bytes of tree, {} nodes, {} shared, {} differ", gOutModules.len(), bytes,
             nodes, gGraftShared, bad);
    flushErr();
    return bad;
}

// One module's section, appended to `out`. After the compile: the facts are the last of it.
pub writeModuleSection inout out:Encoder om:OutModule -> void {
    ops: Encoder;
    opsOfModule(om.mod, &ops);
    view: [u8] = "";
    unsafe { view = ops.view(); }
    putChunk(&out, CHUNK_OPS, view);
    unsafe { view = gOutDecls.view(); }
    putChunk(&out, CHUNK_DECLS, view[om.declsAt..om.declsAt + om.declsLen]);
    facts: Encoder;
    facts.putLen(om.fnCount);
    for k in 0..om.fnCount {
        src: long = gOutFnSrc.get(om.firstFn + k);
        fi: long = -1;
        if (src < gOutFnFactAt.len()) { fi = gOutFnFactAt.get(src); }
        if (fi < 0) { facts.putU8(0); }
        else { facts.putU8(1); putFnFact(&facts, fi); }
    }
    facts.putLen(om.globalCount);
    for k in 0..om.globalCount {
        gi: long = gOutFacts.globalFact(gOutGlobals.get(om.firstGlobal + k));
        if (gi < 0) { failStr(format("internal compiler error: no fact for the global `{}`", nameOf(gOutGlobals.get(om.firstGlobal + k)))); }
        gf: GlobalFact = gOutFacts.globals.get(gi);
        r: GlobalFactRec = GlobalFactRec { name: gf.name, state: gf.state, value: gf.value, image: gf.image };
        r.encode(facts);
    }
    unsafe { view = facts.view(); }
    putChunk(&out, CHUNK_FACTS, view);
    ix: Encoder;
    ix.putLen(om.fnCount);
    for k in 0..om.fnCount {
        ix.putVarint(gOutBodyAt.get(om.firstFn + k));
        ix.putVarint(gOutBodyLen.get(om.firstFn + k));
    }
    unsafe { view = ix.view(); }
    putChunk(&out, CHUNK_BODYIX, view);
    unsafe { view = gOutBodies.view(); }
    putChunk(&out, CHUNK_BODIES, view[om.bodiesAt..om.bodiesAt + om.bodiesLen]);
}

// ─── reading a module ────────────────────────────────────────────────────────

// Where each chunk of one module section is, in it, and what is wrong with its framing ("" when
// nothing is).
pub struct Section { opsAt: long, opsLen: long, declsAt: long, declsLen: long, factsAt: long, factsLen: long,
                     ixAt: long, ixLen: long, bodiesAt: long, bodiesLen: long, bad: str }

pub sectionOf data:[u8] -> Section {
    s: Section = Section { opsAt: 0, opsLen: 0, declsAt: 0, declsLen: 0, factsAt: 0, factsLen: 0,
                           ixAt: 0, ixLen: 0, bodiesAt: 0, bodiesLen: 0, bad: "" };
    d: Decoder;
    unsafe { d = decoderOf(data); }
    while (d.remaining() > 0 && d.ok()) {
        tag: long = d.getUvarint() as long;
        n: long = d.getLen();
        at: long = d.pos;
        d.getRaw(n);
        if (tag == CHUNK_OPS) { s.opsAt = at; s.opsLen = n; }
        else if (tag == CHUNK_DECLS) { s.declsAt = at; s.declsLen = n; }
        else if (tag == CHUNK_FACTS) { s.factsAt = at; s.factsLen = n; }
        else if (tag == CHUNK_BODYIX) { s.ixAt = at; s.ixLen = n; }
        else if (tag == CHUNK_BODIES) { s.bodiesAt = at; s.bodiesLen = n; }
    }
    if (!d.ok()) { s.bad = d.error(); }
    return s;
}

// A module section that cannot be read, which `loadModuleSection` answers with instead of reading
// on. The compile handed the `.klib` stops on it (`Klib.cannotUse`); a build checks a `.klib`'s
// body against its hash before handing it on, so what reaches here was written this way.
local damaged why:str -> KlibCheck {
    return klibDamaged(format("its module section is malformed: {}", why));
}

// ─── loading a module ────────────────────────────────────────────────────────

// How many modules came from a `.klib` already parsed, and how many were parsed here.
pub var gModulesLoaded: long = 0;

// Module `kk` of the loaded `.klib`s, at position `mod` of the scan, into the parser's tree and
// registry, in place of parsing it: its operations replayed, its declarations and bodies read
// into the tree with every index shifted, its top-level statements put on the page (a macro
// where a parsed one would go, after every module), and its facts filed under the indices its
// functions got.
pub loadModuleSection inout p:Parser kk:long mod:long -> KlibCheck {
    km: KlibModule = gKlibModules.get(kk);
    info: KlibInfo = gKlibs.get(km.klib);
    gSymInBase = info.symBase;
    gSymInCount = info.symCount;
    all: [u8] = info.body as [u8];
    data: [u8] = all[info.modulesAt + km.at..info.modulesAt + km.at + km.len];
    s: Section = sectionOf(data);
    if (s.bad.len > 0) { return damaged(s.bad); }

    // The facts first: a constant's value is what the parser reads a length from, and the
    // replay below puts it where the parser looks. A function's are filed once DECLS says where
    // the module's functions are.
    fd: Decoder;
    unsafe { fd = decoderOf(data[s.factsAt..s.factsAt + s.factsLen]); }
    nf: long = fd.getLen();
    facts: Vec<long>;
    facts.reserve(nf);
    k: long = 0;
    while (k < nf && fd.ok()) {
        if (fd.getU8() == 0) { facts.push(-1); }
        else { facts.push(getFnFact(&fd)); }
        k = k + 1;
    }
    ng: long = fd.getLen();
    globals: Vec<GlobalFactRec>;
    k = 0;
    while (k < ng && fd.ok()) {
        g: GlobalFactRec = GlobalFactRec.decode(fd);
        if (g.image >= 0) { g.image = g.image + info.imageBase; }
        gFacts.addGlobal(GlobalFact { name: g.name, state: g.state, value: g.value, image: g.image });
        globals.push(g);
        k = k + 1;
    }
    if (!fd.done()) { return damaged(fd.error()); }

    // The registry, as the module's parse wrote it.
    file: Sym = intern(km.path);
    rp: Replay = replayOf(file, intern(km.pkg), true);
    rb: Rebase = rebaseOf();
    od: Decoder;
    unsafe { od = decoderOf(data[s.opsAt..s.opsAt + s.opsLen]); }
    rp.run(&od, &p.fnReturns, &p.ast, &rb.bounds);
    if (!od.done()) { return damaged(od.error()); }
    // An integer constant's initializer is not carried, but the value it folded to is, and a
    // length written `nums::BASE` in a dependent is read from the declaration's initializer.
    for folded in globals {
        if (folded.state != GlobalState.Scalar) { continue; }
        gi: long = gReg.findGlobalSym(folded.name);
        if (gi < 0) { continue; }
        def: GlobalDef = gReg.globalDef(gi);
        if (def.isVar || def.isArray || !isInteger(def.kind)) { continue; }
        def.init = p.ast.leaf(Op.Literal, Payload.Num(folded.value), def.kind);
        gReg.globals.set(gi, def);
    }

    // The declarations.
    rb.startAt(p.ast);
    rb.fnBase = p.ast.fns.len();
    dd: Decoder;
    unsafe { dd = decoderOf(data[s.declsAt..s.declsAt + s.declsLen]); }
    decodeTree(&dd, &p.ast, &rb);
    roots: Vec<long> = decodeVec(&dd);
    defs: Vec<bool> = decodeVec(&dd);
    if (!dd.done() || roots.len() != defs.len()) { return damaged(dd.error()); }
    stmtBase: long = rb.base.get(Arena.Stmts as long);
    for k in 0..roots.len() {
        st: long = roots.get(k) + stmtBase;
        if (defs.get(k)) { p.noteLoadedMacro(st, mod); } else { p.notePage(st, mod, false); }
    }
    fnBase: long = rb.fnBase;
    nfn: long = p.ast.fns.len() - fnBase;
    if (nfn != facts.len()) { return damaged("the facts do not match the functions"); }

    // The bodies, each its own tree: a template's and a macro's read now (stamping an instance
    // and running a macro need them), every other one when something needs it (`ensureBody`).
    xd: Decoder;
    unsafe { xd = decoderOf(data[s.ixAt..s.ixAt + s.ixLen]); }
    n: long = xd.getLen();
    if (n != nfn) { return damaged("the body index does not match the functions"); }
    bodies: [u8] = data[s.bodiesAt..s.bodiesAt + s.bodiesLen];
    bodiesAt: long = 0;
    unsafe { bodiesAt = bodies.ptr as long; }
    k = 0;
    while (k < n && xd.ok()) {
        at: long = xd.getVarint();
        len: long = xd.getVarint();
        if (at >= 0) {
            if (at + len > bodies.len) { return damaged("a body past the end of its chunk"); }
            fi: long = fnBase + k;
            f: FnNode = p.ast.fns.get(fi);
            noteLazyBody(fi, LazyBody { at: bodiesAt + at, len: len, symBase: info.symBase, symCount: info.symCount,
                                        fnBase: fnBase, origin: info.path });
            if (f.isTemplate || gReg.isMacro(f.name)) { ensureBody(&p.ast, fi); }
        }
        k = k + 1;
    }
    if (!xd.done()) { return damaged(xd.error()); }
    for k in 0..nfn {
        if (facts.get(k) >= 0) { noteFnFact(fnBase + k, facts.get(k)); }
    }
    gModulesLoaded = gModulesLoaded + 1;
    if (gOpLogOn) { gOpOrder.push(-1 - kk); }
    return klibUsable();
}

// The registry replayed from nothing in the order the compile applied it: this package's own
// operations and every loaded module's, and compared with the one the compile has.
pub verifyPackageRegops inout p:Parser -> long {
    opsEnd();
    ownSymsReadable();
    parts: Vec<OpPart>;
    for o in gOpOrder {
        if (o >= 0) { parts.push(logPart(o)); continue; }
        km: KlibModule = gKlibModules.get(-1 - o);
        info: KlibInfo = gKlibs.get(km.klib);
        all: [u8] = info.body as [u8];
        data: [u8] = all[info.modulesAt + km.at..info.modulesAt + km.at + km.len];
        s: Section = sectionOf(data);
        at: long = 0;
        unsafe { at = data.ptr as long; }
        parts.push(OpPart { at: at + s.opsAt, len: s.opsLen, symBase: info.symBase, symCount: info.symCount,
                            file: intern(km.path), pkg: intern(km.pkg), upstream: true });
    }
    return verifyRegopsParts(&p.ast, p.fnReturns, parts);
}

// A vector as `Vec`'s codec writes it, its element type taken from where it is stored.
pub decodeVec<T: Decode> inout d:Decoder -> Vec<T> {
    n: long = d.getLen();
    v: Vec<T>;
    v.reserve(n);
    for k in 0..n { v.push(T.decode(d)); }
    return v;
}
