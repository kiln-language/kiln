// A syntax tree as bytes, and back: the form a `.klib` carries a module's declarations and each
// function body in (`1-cumulation/KlibTree.k` writes and reads the sections; this is the part
// every phase may need, since a dependency's body is read only when something needs it).
//
// A tree is dense and starts at zero in every arena. Writing one puts a bitmask of the arenas
// present, then each present arena: its length, then its elements, every index field as it is.
// Reading one shifts every index by where that arena starts in the reader's tree (`Rebase`),
// node by node through `ast.k`'s `mapX`, as it is pushed.
#include <ast>
#include <support::compiler>
#include <stdlib::{encode, map, option, string, vec}>

// ─── a tree, as bytes ────────────────────────────────────────────────────────
// A bitmask of the arenas present, then each present one: its length, then its elements. Index
// fields are written as they are, relative to this tree.

pub encodeTree inout e:Encoder a:Ast -> void {
    mask: long = 0;
    for k in 0..Arena.Bounds as long {
        if (columnLen(a, k as Arena) > 0) { mask = mask | (1 << k); }
    }
    e.putUvarint(mask as u64);
    if (a.exprs.len() > 0) { a.exprs.encode(e); }
    if (a.indexes.len() > 0) { a.indexes.encode(e); }
    if (a.calls.len() > 0) { a.calls.encode(e); }
    if (a.fields.len() > 0) { a.fields.encode(e); }
    if (a.lits.len() > 0) { a.lits.encode(e); }
    if (a.inits.len() > 0) { a.inits.encode(e); }
    if (a.args.len() > 0) { a.args.encode(e); }
    if (a.stmts.len() > 0) { a.stmts.encode(e); encodePositions(e, a); }
    if (a.blocks.len() > 0) { a.blocks.encode(e); }
    if (a.stmtRuns.len() > 0) { a.stmtRuns.encode(e); }
    if (a.ifs.len() > 0) { a.ifs.encode(e); }
    if (a.whiles.len() > 0) { a.whiles.encode(e); }
    if (a.returns.len() > 0) { a.returns.encode(e); }
    if (a.blockStmts.len() > 0) { a.blockStmts.encode(e); }
    if (a.withs.len() > 0) { a.withs.encode(e); }
    if (a.exprStmts.len() > 0) { a.exprStmts.encode(e); }
    if (a.destructures.len() > 0) { a.destructures.encode(e); }
    if (a.names.len() > 0) { a.names.encode(e); }
    if (a.arms.len() > 0) { a.arms.encode(e); }
    if (a.matches.len() > 0) { a.matches.encode(e); }
    if (a.asms.len() > 0) { a.asms.encode(e); }
    if (a.asmPieces.len() > 0) { a.asmPieces.encode(e); }
    if (a.decls.len() > 0) { a.decls.encode(e); }
    if (a.params.len() > 0) { a.params.encode(e); }
    if (a.fns.len() > 0) { a.fns.encode(e); }
    if (a.structDecls.len() > 0) { a.structDecls.encode(e); }
}

// Where each statement stands, after the statements: a file index means nothing in another
// process, so the file crosses as a name through the string table, and only when it changes
// (a module's statements are all one file's). Per statement: 0 for no position; 1 for the file
// before; otherwise the file's table place plus 2. Then the line and the column.
pub encodePositions inout e:Encoder a:Ast -> void {
    last: Sym = NO_SYM;
    for k in 0..a.stmtPos.len() {
        p: long = a.stmtPos.get(k);
        f: Sym = posFile(p);
        if (f == NO_SYM) { e.putUvarint(0); continue; }
        if (f == last) { e.putUvarint(1); }
        else { e.putUvarint((symOut(f) + 2) as u64); last = f; }
        e.putUvarint(posLine(p) as u64);
        e.putUvarint(posCol(p) as u64);
    }
}

pub decodePositions inout d:Decoder inout a:Ast n:long -> void {
    a.stmtPos.reserve(n);
    last: Sym = NO_SYM;
    for k in 0..n {
        t: long = d.getUvarint() as long;
        if (t == 0) { a.stmtPos.push(0); continue; }
        if (t > 1) { last = symAt(d, t - 1); }
        line: long = d.getUvarint() as long;
        col: long = d.getUvarint() as long;
        a.stmtPos.push(posOf(last, line, col));
    }
}

pub columnLen a:Ast k:Arena -> long {
    match k {
        Exprs        { return a.exprs.len(); }
        Indexes      { return a.indexes.len(); }
        Calls        { return a.calls.len(); }
        Fields       { return a.fields.len(); }
        Lits         { return a.lits.len(); }
        Inits        { return a.inits.len(); }
        Args         { return a.args.len(); }
        Stmts        { return a.stmts.len(); }
        Blocks       { return a.blocks.len(); }
        StmtRuns     { return a.stmtRuns.len(); }
        Ifs          { return a.ifs.len(); }
        Whiles       { return a.whiles.len(); }
        Returns      { return a.returns.len(); }
        BlockStmts   { return a.blockStmts.len(); }
        Withs        { return a.withs.len(); }
        ExprStmts    { return a.exprStmts.len(); }
        Destructures { return a.destructures.len(); }
        Names        { return a.names.len(); }
        Arms         { return a.arms.len(); }
        Matches      { return a.matches.len(); }
        Asms         { return a.asms.len(); }
        AsmPieces    { return a.asmPieces.len(); }
        Decls        { return a.decls.len(); }
        Params       { return a.params.len(); }
        Fns          { return a.fns.len(); }
        StructDecls  { return a.structDecls.len(); }
        _            { return 0; }
    }
}

// ─── reading: the rebase ─────────────────────────────────────────────────────

// Where each arena of a tree being read starts in the reader's: the length it had before. A
// function is DECLS's wherever it is named (`fnBase`), and its bounds are the registry's, as the
// replay of the module's operations placed them (`bounds`), or as written (`sameBounds`, a tree
// read back in the process that wrote it).
pub struct Rebase { base: Vec<long>, fnBase: long, bounds: HashMap<long, long>, sameBounds: bool }

pub rebaseOf -> Rebase {
    return Rebase { base: vec![], fnBase: 0, bounds: map![], sameBounds: false };
}

methods Rebase {
    // Every arena's base, from the tree as it stands now.
    startAt &self a:Ast -> void {
        self.base.clear();
        for k in 0..(Arena.Nowhere as long) + 1 { self.base.push(columnLen(a, k as Arena)); }
    }
}

methods Rebase for IdMap {
    id &self src:Ast arena:Arena v:long -> long {
        if (v < 0 || arena == Arena.Nowhere) { return v; }
        if (arena == Arena.Fns) { return v + self.fnBase; }
        if (arena == Arena.Bounds) {
            if (self.sameBounds) { return v; }
            hit: Option<long> = self.bounds.find(v);
            match hit { Some(i) { return i; } None { } }
            failStr(format("internal: a function's bounds ({}) were not among its module's operations", v));
            return v;
        }
        return v + self.base.get(arena as long);
    }
    run &self src:Ast arena:Arena first:long count:long -> long {
        return first + self.base.get(arena as long);
    }
}

// One tree read into `a`, each node rebased as it is pushed. `rb` must have been started on `a`
// (`startAt`) and given its function base.
pub decodeTree inout d:Decoder inout a:Ast inout rb:Rebase -> void {
    none: Ast;
    mask: long = d.getUvarint() as long;
    n: long = 0;
    if ((mask & (1 << (Arena.Exprs as long))) != 0) {
        n = d.getLen(); a.exprs.reserve(n);
        for k in 0..n { x: Expr = Expr.decode(d); a.exprs.push(mapExpr(x, rb, none)); }
    }
    if ((mask & (1 << (Arena.Indexes as long))) != 0) {
        n = d.getLen(); a.indexes.reserve(n);
        for k in 0..n { x: IndexNode = IndexNode.decode(d); a.indexes.push(mapIndex(x, rb, none)); }
    }
    if ((mask & (1 << (Arena.Calls as long))) != 0) {
        n = d.getLen(); a.calls.reserve(n);
        for k in 0..n { x: CallNode = CallNode.decode(d); a.calls.push(mapCall(x, rb, none)); }
    }
    if ((mask & (1 << (Arena.Fields as long))) != 0) {
        n = d.getLen(); a.fields.reserve(n);
        for k in 0..n { x: FieldNode = FieldNode.decode(d); a.fields.push(mapField(x, rb, none)); }
    }
    if ((mask & (1 << (Arena.Lits as long))) != 0) {
        n = d.getLen(); a.lits.reserve(n);
        for k in 0..n { x: LitNode = LitNode.decode(d); a.lits.push(mapLit(x, rb, none)); }
    }
    if ((mask & (1 << (Arena.Inits as long))) != 0) {
        n = d.getLen(); a.inits.reserve(n);
        for k in 0..n { x: InitNode = InitNode.decode(d); a.inits.push(mapInit(x, rb, none)); }
    }
    if ((mask & (1 << (Arena.Args as long))) != 0) {
        n = d.getLen(); a.args.reserve(n);
        for k in 0..n { a.args.push(rb.id(none, Arena.Exprs, d.getVarint())); }
    }
    if ((mask & (1 << (Arena.Stmts as long))) != 0) {
        n = d.getLen(); a.stmts.reserve(n);
        for k in 0..n { x: Stmt = Stmt.decode(d); a.stmts.push(mapStmt(x, rb, none)); }
        decodePositions(d, a, n);
    }
    if ((mask & (1 << (Arena.Blocks as long))) != 0) {
        n = d.getLen(); a.blocks.reserve(n);
        for k in 0..n { x: Block = Block.decode(d); a.blocks.push(mapBlock(x, rb, none)); }
    }
    if ((mask & (1 << (Arena.StmtRuns as long))) != 0) {
        n = d.getLen(); a.stmtRuns.reserve(n);
        for k in 0..n { a.stmtRuns.push(rb.id(none, Arena.Stmts, d.getVarint())); }
    }
    if ((mask & (1 << (Arena.Ifs as long))) != 0) {
        n = d.getLen(); a.ifs.reserve(n);
        for k in 0..n { x: IfNode = IfNode.decode(d); a.ifs.push(mapIf(x, rb, none)); }
    }
    if ((mask & (1 << (Arena.Whiles as long))) != 0) {
        n = d.getLen(); a.whiles.reserve(n);
        for k in 0..n { x: WhileNode = WhileNode.decode(d); a.whiles.push(mapWhile(x, rb, none)); }
    }
    if ((mask & (1 << (Arena.Returns as long))) != 0) {
        n = d.getLen(); a.returns.reserve(n);
        for k in 0..n { x: ReturnNode = ReturnNode.decode(d); a.returns.push(mapReturn(x, rb, none)); }
    }
    if ((mask & (1 << (Arena.BlockStmts as long))) != 0) {
        n = d.getLen(); a.blockStmts.reserve(n);
        for k in 0..n { x: BlockStmtNode = BlockStmtNode.decode(d); a.blockStmts.push(mapBlockStmt(x, rb, none)); }
    }
    if ((mask & (1 << (Arena.Withs as long))) != 0) {
        n = d.getLen(); a.withs.reserve(n);
        for k in 0..n { x: WithNode = WithNode.decode(d); a.withs.push(mapWith(x, rb, none)); }
    }
    if ((mask & (1 << (Arena.ExprStmts as long))) != 0) {
        n = d.getLen(); a.exprStmts.reserve(n);
        for k in 0..n { x: ExprStmtNode = ExprStmtNode.decode(d); a.exprStmts.push(mapExprStmt(x, rb, none)); }
    }
    if ((mask & (1 << (Arena.Destructures as long))) != 0) {
        n = d.getLen(); a.destructures.reserve(n);
        for k in 0..n { x: DestructureNode = DestructureNode.decode(d); a.destructures.push(mapDestructure(x, rb, none)); }
    }
    if ((mask & (1 << (Arena.Names as long))) != 0) {
        n = d.getLen(); a.names.reserve(n);
        for k in 0..n { a.names.push(Sym.decode(d)); }
    }
    if ((mask & (1 << (Arena.Arms as long))) != 0) {
        n = d.getLen(); a.arms.reserve(n);
        for k in 0..n { x: ArmNode = ArmNode.decode(d); a.arms.push(mapArm(x, rb, none)); }
    }
    if ((mask & (1 << (Arena.Matches as long))) != 0) {
        n = d.getLen(); a.matches.reserve(n);
        for k in 0..n { x: MatchNode = MatchNode.decode(d); a.matches.push(mapMatch(x, rb, none)); }
    }
    if ((mask & (1 << (Arena.Asms as long))) != 0) {
        n = d.getLen(); a.asms.reserve(n);
        for k in 0..n { x: AsmNode = AsmNode.decode(d); a.asms.push(mapAsm(x, rb, none)); }
    }
    if ((mask & (1 << (Arena.AsmPieces as long))) != 0) {
        n = d.getLen(); a.asmPieces.reserve(n);
        for k in 0..n { x: AsmPiece = AsmPiece.decode(d); a.asmPieces.push(mapAsmPiece(x, rb, none)); }
    }
    if ((mask & (1 << (Arena.Decls as long))) != 0) {
        n = d.getLen(); a.decls.reserve(n);
        for k in 0..n { x: VarDeclNode = VarDeclNode.decode(d); a.decls.push(mapDecl(x, rb, none)); }
    }
    if ((mask & (1 << (Arena.Params as long))) != 0) {
        n = d.getLen(); a.params.reserve(n);
        for k in 0..n { a.params.push(rb.id(none, Arena.Decls, d.getVarint())); }
    }
    if ((mask & (1 << (Arena.Fns as long))) != 0) {
        n = d.getLen(); a.fns.reserve(n);
        for k in 0..n { x: FnNode = FnNode.decode(d); a.fns.push(mapFn(x, rb, none)); }
    }
    if ((mask & (1 << (Arena.StructDecls as long))) != 0) {
        n = d.getLen(); a.structDecls.reserve(n);
        for k in 0..n { a.structDecls.push(Sym.decode(d)); }
    }
}


// ─── a dependency's bodies, read when needed ────────────────────────────────
// A dependency's function is not checked, lowered or emitted here, so its body is wanted only
// when compile-time code reaches it (the checker checks it then, `Checker.ctNeed`). Its node says
// `BODY_LAZY` until then, and where its tree is in the `.klib` is kept here: reading it then costs
// what it would have cost up front, and a body nothing reaches costs nothing. Templates and
// macros are read with their module, since stamping an instance or running a macro needs one.

// Where one body is: its bytes (a view of the kept metadata), the string table its names are in,
// and where its module's functions start in the tree.
pub struct LazyBody { at: long, len: long, symBase: long, symCount: long, fnBase: long, origin: str }

pub var gLazyBodies: Vec<LazyBody> = vec![];
pub var gLazyAt: Vec<long> = vec![];       // per function of the tree: its entry above, or -1
pub var gBodiesRead: long = 0;              // read when something needed them

pub noteLazyBody fi:long b:LazyBody -> void {
    while (gLazyAt.len() <= fi) { gLazyAt.push(-1); }
    gLazyAt.set(fi, gLazyBodies.len());
    gLazyBodies.push(b);
}

// Function `fi`'s body, read into the tree if it has not been. Answers the function as it is now.
pub ensureBody inout a:Ast fi:long -> FnNode {
    f: FnNode = a.fns.get(fi);
    if (f.body != BODY_LAZY) { return f; }
    if (fi >= gLazyAt.len() || gLazyAt.get(fi) < 0) {
        failStr(format("internal: '{}' has a body in its .klib and nothing says where", nameOf(f.name)));
    }
    b: LazyBody = gLazyBodies.get(gLazyAt.get(fi));
    gLazyAt.set(fi, -1);
    wasBase: long = gSymInBase;
    wasCount: long = gSymInCount;
    gSymInBase = b.symBase;
    gSymInCount = b.symCount;
    view: [u8] = "";
    unsafe { view = (b.at as *u8)[..b.len]; }
    d: Decoder = decoderOf(view);
    rb: Rebase = rebaseOf();
    rb.startAt(a);
    rb.fnBase = b.fnBase;
    decodeTree(&d, a, &rb);
    root: long = d.getVarint() + rb.base.get(Arena.Blocks as long);
    if (!d.done()) { failStr(format("{}: damaged .klib metadata ({}) -- rebuild it", b.origin, d.error())); }
    gSymInBase = wasBase;
    gSymInCount = wasCount;
    f.body = root;
    a.fns.set(fi, f);
    gBodiesRead = gBodiesRead + 1;
    return f;
}
