// The syntax tree.
//
// Every node lives in one arena and is named by an index, not a pointer. Recursion is by `NodeId`,
// so no type here refers to itself, nothing needs `Box`, and every node is Copy. The
// variable-length parts are runs in flat vectors rather than a vector per node.
#include <support::compiler>
#include <stdlib::{encode, vec}>

pub type NodeId = long;
pub NO_NODE: NodeId = -1;

// The type of a local the parser declares without knowing it (`_ = f();`'s hidden local, the
// subject of a `match` on an expression): `Lit.Void` named `$infer`. The checker gives it the
// type of what its first store holds, and rewrites the declaration to say so; nothing after the
// checker ever sees one.
pub INFER_SPELLING: str = "$infer";

// ─── types ───────────────────────────────────────────────────────────────────

pub enum Lit: int {
    Int, Long, Char,
    Float, Double,
    Str,                // a string slice: a fat pointer {ptr, len}
    Slice,              // `[T]`: a fat pointer over `len` elements of T
    Any,                // a dynamic value: a 24-byte tagged box {tag, x, y}
    Tuple,              // a structural aggregate (T, U, ...)
    Struct,             // a named aggregate
    TraitObj,           // a fat pointer {data, vtable}
    TypeVar,            // a generic parameter, only inside a template
    Ref,                // an 8-byte pointer to a shared struct
    Fn,                 // a function pointer
    I16, U8, U16, U32, U64,
    Bool,
    Ptr,                // *T: the pointee rides in the companion name
    Void,
    // Not a type: a length standing where a template takes one, `Buf<64>` or the default of
    // `N: long = 4096`. The companion is the value's decimal spelling, which is also how it is
    // mangled into an instance's name (`Buf_64`). Only ever a template argument.
    Len
}

// How a function accesses an aggregate parameter (mutable value semantics):
//   Read:  read-only for the call's duration; passes a pointer, no copy, no writes.
//   Inout: exclusive in-place mutation; the caller lends with `&x` and sees the writes.
//   Sink:  the callee gets its own value, a copy of plain data or a move of a Drop value.
//   None:  unannotated; the compiler infers Read or Sink from what the body does.
pub enum Conv: int { None, Read, Inout, Sink }

pub enum Vis: int { Local, Pkg, Pub }

// ─── expressions ─────────────────────────────────────────────────────────────

pub enum Op: int {
    Assignment,

    Addition, Subtraction, Multiplication, Division, Modulus,

    LessThan, GreaterThan,
    IsLessOrEqual, IsGreaterOrEqual, IsEqual, IsNotEqual,

    BitwiseAnd, BitwiseOr, BitwiseXor,
    ShiftLeft, ShiftRight,          // ShiftRight is arithmetic
    LogicalAnd, LogicalOr,          // short-circuit

    BitwiseNot, LogicalNot,         // prefix; operand in `value`

    FunctionCall,
    Lvalue,
    ArrayIndex,
    Cast,                           // expr as type; operand in `value`
    AddressOf,                      // &name / &a.b.c
    StringLit,
    TupleLit,
    FieldAccess,
    StructLit,
    MethodCall,
    Sizeof,                         // the byte size of a type, named by `lit`/`structName`
    // `nameof(E, v)`: the name of the variant `v` holds, as a str. The enum is in `structName`,
    // the value in the payload. Rewritten by the checker into a call to a derived `E_nameof`.
    Nameof,
    Splice,                         // `@x` inside a quote: the Node that `x` holds goes here; `Name(x)`
    // `name!(args)`: a call the compiler runs while checking, replacing it with what the macro
    // returned (a value, or a `Node` spliced in as code). Carries a `Call`. It never reaches the
    // lowerer, because the checker expands every one.
    MacroCall,
    Deref,                          // *p: load or store through a typed pointer
    Literal,
    // An aggregate computed at compile time: the bytes of the value, with the pointer words in
    // them named (`images`). Only ever a global's initializer, put there by the evaluator; the
    // lowerer emits it as data and runs nothing for it.
    Image,
    // A concrete value viewed as a trait object: `{data, vtable}`. Inserted by the checker
    // where a struct meets a trait-typed parameter or variable, never written in source. The
    // operand keeps its own type, which is how lowering knows which vtable to point at; this
    // node's `structName` is the trait.
    MakeTraitObj,
    // `[a, b, c]`: an array's elements, in a `Lit` payload as a tuple's are. Only an array
    // declaration's initializer: a local's is written out by the parser as one store per
    // element, so only a global's reaches the checker, which holds each element to the array's
    // type, and the evaluator, which builds it; `kind`/`structName` are the element's type.
    ArrayLit
}

// The four that order. `==` and `!=` are comparisons too but answer to a different contract.
// Here, with the operators, rather than with the checker that asks first: the lowerer asks too,
// and a function is reached through what its caller's module includes.
pub isRelational op:Op -> bool {
    return op == Op.LessThan || op == Op.GreaterThan
        || op == Op.IsLessOrEqual || op == Op.IsGreaterOrEqual;
}

// Whether a value is a truth value, whatever width the checker gave it: a `bool`, or what `!`,
// a comparison, `&&` and `||` make (each typed `int`, 0 or 1). What `{}` shows as true/false.
pub isTruthValue kind:Lit op:Op -> bool {
    return kind == Lit.Bool || isComparison(op) || op == Op.LogicalNot
        || op == Op.LogicalAnd || op == Op.LogicalOr;
}

pub isInferType k:Lit n:Sym -> bool { return k == Lit.Void && n != NO_SYM && nameOf(n) == INFER_SPELLING; }

pub isComparison op:Op -> bool {
    return op == Op.LessThan || op == Op.GreaterThan || op == Op.IsLessOrEqual
        || op == Op.IsGreaterOrEqual || op == Op.IsEqual || op == Op.IsNotEqual;
}

// What an expression node carries besides its operands. The payloads are all indices and symbols,
// so this stays Copy.
pub enum Payload {
    None,
    Num(long),                      // Literal: the value
    Text(Sym),                      // StringLit: the raw source spelling, escapes unresolved
    Name(Sym),                      // Lvalue / AddressOf: the variable
    Index(long),                    // ArrayIndex: into the arena's `indexes`
    Call(long),                     // FunctionCall / MethodCall: into `calls`
    Field(long),                    // FieldAccess: into `fields`
    Lit(long),                      // StructLit / TupleLit: into `lits`
    Sub(NodeId),                    // Cast / Deref / the unary operators: the operand
    Image(long)                     // Image: into `images`
}

pub struct Expr {
    op:    Op,
    left:  NodeId,      // NO_NODE for anything that is not a binary operator
    right: NodeId,
    kind:  Lit,         // the type this expression yields
    structName: Sym,    // set when `kind` names an aggregate, a pointee, or a trait
    isParen: bool,
    payload: Payload
}

// `name[index]`, and the whole-array form `name[..]`.
// `a[i]` reads one element (`index`); `a[lo..hi]` takes a slice of it (`whole`, with either
// bound optional: a missing `lo` is 0, a missing `hi` is the base's own length, which an array
// or a slice knows and a raw pointer does not).
// `at` is where the brackets were written, as `<file>:<line>`. It is kept because a bounds check
// that fails does so at runtime, with no compiler left to say where the index came from: the
// position has to ride into the emitted program or the message cannot name it. NO_SYM for an
// index the compiler synthesized, which has no line of its own to give.
pub struct IndexNode { name: Sym, base: NodeId, index: NodeId, whole: bool, rawPointerBase: bool,
                       sliceStart: NodeId, sliceEnd: NodeId, at: Sym }

// What the parser read between the brackets, before it knows whose index it is. A plain struct
// rather than four returns, because a method may return only one value.
pub struct IndexParts { index: NodeId, lo: NodeId, hi: NodeId, whole: bool }

// A call: a name, and its arguments as a run. `receiver` is NO_NODE for a plain function call and
// the object for a method call.
// `slot` is -1 for an ordinary call and the vtable index for one dispatched through a trait
// object, which the checker fills in once it knows the receiver is one.
// `callee` is the expression the call goes through when the thing being called has no name of
// its own: a fn-typed struct field, `t.apply(v)`. A named fn-typed local is reached by `name`;
// everything else needs the expression, because there is nothing to look up.
// `sigKey` is the signature an indirect call goes through, NO_SYM for a direct one. Such a call
// has no callee definition to read a convention out of (that is what makes it indirect), so
// what the pointer's own type promises is the only thing that says whether an argument is lent
// or handed over. It is written down here, at the call, because the ownership walk runs long
// after the expression that named the pointer left the checker's scope.
pub struct CallNode { name: Sym, receiver: NodeId, firstArg: long, argCount: long, slot: long,
                      callee: NodeId, sigKey: Sym }

pub NO_SLOT: long = -1;
// The callee is not a name at all but a fn-typed variable holding its address: `f(x)` where
// `f: fn(long)->long`. It dispatches indirectly like a trait method, so it rides the same field.
pub SLOT_FNPTR: long = -2;

// `p.x`: a field of any struct-typed expression. A chain `a.b.c` nests through `base`.
pub struct FieldNode { base: NodeId, name: Sym }

// A struct or tuple literal: the named type, and its initializers as a run. A tuple names nothing.
// `P { a: 1, ..other }`: `rest` is the value every field not named comes from, or NO_NODE when
// the literal names them all. Only the naming-them-all form may build a value that owns
// something: copying the rest of a Drop struct would hand two owners the same buffer.
pub struct LitNode { typeName: Sym, firstInit: long, initCount: long, rest: NodeId }

// One `field: value` in a struct literal. A tuple literal leaves the name unset.
pub struct InitNode { name: Sym, value: NodeId }

// A value's bytes as computed at compile time, and where inside them a word is a pointer. A
// global's image is emitted at the global's own label; a heap block's image is emitted as a
// labeled block of its own, which is what a pointer to it relocates to. The word at `offset`
// points `delta` bytes past the string literal spelled `target` (Str), the block `image` (Block)
// or the global named `target` (Global), or exactly at the vtable or function labeled `target`.
pub enum RelocKind: int { Str, Block, Global, Vtable, Fn }
pub struct ImageNode { firstByte: long, byteCount: long, firstReloc: long, relocCount: long, isBlock: bool }
pub struct RelocNode { offset: long, kind: RelocKind, target: Sym, image: long, delta: long }

// ─── statements ──────────────────────────────────────────────────────────────

pub enum StmtKind: int {
    FunctionDef, VarDecl, If, Loop, While, With, Unsafe, Return,
    Call, Expr, Asm, Destructure, Break, Continue, Match, StructDecl,
    Block,         // a bare nested block: its own scope, run once
    // `recover { body } else { handler }`: a `raise` anywhere under the body resumes in the
    // handler. Its node is a `WhileNode` with no condition, the body in `body` and the handler in
    // `step`, so it lives in a side table every pass already copies, remaps and encodes.
    Recover
}

// A statement is its kind plus one payload index, into whichever side table that kind uses. The
// kinds that carry nothing (`break`, `continue`) use neither.
pub struct Stmt { kind: StmtKind, at: long }

// A block: a run of statements.
pub struct Block { firstStmt: long, stmtCount: long }

pub struct IfNode { cond: NodeId, body: long, elseIf: long }        // block ids; elseIf is an IfNode
pub struct WhileNode { cond: NodeId, body: long, step: long }       // `step` makes a `for` a while
pub struct ReturnNode { value: NodeId }
pub struct BlockStmtNode { body: long }                             // `loop`, `unsafe`
pub struct WithNode { name: Sym, body: long }
pub struct ExprStmtNode { value: NodeId }

// `q, r = divmod(10, 3);`: a tuple-returning call unpacked into fresh scalars.
pub struct DestructureNode { firstName: long, nameCount: long, value: NodeId }

// One arm of a `match`: the variant it answers for, the names it binds the payload to, and its
// block. `variant` is NO_SYM for the wildcard `_`, which covers every variant not named.
// `test` is `subject.$tag == <variant>`, built by the parser because that is where the
// variant's value is known. The last arm's is NO_NODE: it is reached by elimination.
pub struct ArmNode { variant: Sym, test: NodeId, firstBind: long, bindCount: long, body: long }
pub struct MatchNode { scrutinee: Sym, firstArm: long, armCount: long }

// Inline assembly, the language's one escape hatch to raw instructions:
//
//   asm {
//       in <reg> <expr>;      evaluate expr and place it in <reg> before the block
//       "literal asm line"    emitted verbatim, in order
//       out <var> <reg>;      after the block, store <reg> into <var>
//   }
//
// The register allocator treats the block like a call: it clobbers the caller-saved registers, so
// anything that must survive it is kept elsewhere, which is why every register named here must
// itself be caller-saved.
pub enum AsmKind: int { In, Out, Text }

pub struct AsmPiece { kind: AsmKind, reg: Sym, name: Sym, value: NodeId, text: Sym }

// `asm -> never { ... }`: a block that does not come back (an `exit` syscall, `ud2`), which ends
// its path for every check that follows paths, as a call to a `-> never` function does.
pub struct AsmNode { firstPiece: long, pieceCount: long, noReturn: bool }

pub struct VarDeclNode {
    name: Sym,
    kind: Lit,          // scalar: the type; array: the element type
    structName: Sym,
    isArray: bool,
    count: long,        // elements, arrays only
    conv: Conv,
    isVariadic: bool,
    elemKind: Lit,      // slice and variadic parameters describe their element here
    elemStruct: Sym,
    init: NodeId        // NO_NODE for a bare declaration
}

pub struct FnNode {
    name: Sym,
    returnKind: Lit,
    returnStruct: Sym,
    visibility: Vis,
    file: Sym,
    pkg: Sym,
    isUnsafe: bool,
    // A method of a generic type, whose parameter types are still `TypeVar`. It is a pattern,
    // not code: monomorphization clones it per instance and those clones are what gets emitted.
    // Left in the tree because the clones are made from it, and skipped by everything after.
    isTemplate: bool,
    // `methods BufWriter<W: Default>` applies only to instances whose W is Default. The bounds
    // belong to the block, so every method in one shares this range into the registry's list.
    firstBound: long, boundCount: long,
    firstArg: long, argCount: long,     // into `params`
    body: long,                         // a block id
    // A closure's expression body: the return type is whatever that expression turns out to be,
    // which only the checker knows. Written declarations always say.
    inferReturn: bool,
    // What the declaration says beyond its signature (`FN_NEVER`, `FN_INIT`, ...), and for a
    // `builtin` the primitive the compiler provides for it (`builtinOf`).
    attrs: long
}

// `-> never`: the function does not come back (the checker holds its body to that), so a call to
// it ends a path for definite initialization, ownership, the return check and the optimizer.
pub FN_NEVER: long = 1;
// `@init` / `@fini`: run once before `main` / once after it returns or the program calls the
// `exit` builtin, every package's in dependency order (`fini` in reverse).
pub FN_INIT: long = 2;
pub FN_FINI: long = 4;
// `@panic`: what the code the compiler writes for a failed `assert!` calls with its message.
pub FN_PANIC: long = 8;
// `@recover`: what a `recover` statement calls to link its record into this thread's chain and
// to unlink it again (`rec:long -> long`, answering the record it replaced).
pub FN_RECOVER: long = 16;
// `@spill`: what the code the compiler writes for a failed bounds check calls before its report,
// to write out what the program holds back for stdout (`name -> void`). It must take no lock: the
// failing thread may hold one.
pub FN_SPILL: long = 32;
// `builtin name params -> T;`: a declaration whose body the compiler provides. Which primitive is
// in the bits above `BUILTIN_SHIFT`, one of the `BI_` kinds.
pub BUILTIN_SHIFT: long = 8;
pub BI_SYSCALL: long = 1;        // syscall(nr, args...) -> long: the `syscall` instruction
pub BI_AT_COMPILE_TIME: long = 2; // atCompileTime() -> bool: true in the evaluator, false at run time
pub BI_PARSE_EXPR: long = 3;     // parseExpr(src) -> Node: the compiler's parser, in a macro
pub BI_EXIT: long = 4;           // exit(status) -> never: the `@fini` hooks, then exit_group
// The atomics: one instruction each on an eight-byte word (`*long`), and the same six on a
// four-byte one (`*int`, `BI_ATOMIC_32` past them). Which operation is `atomicOpOf`.
pub BI_ATOMIC_LOAD: long = 5;       // atomicLoad(p) -> long: acquire, `mov`
pub BI_ATOMIC_STORE: long = 6;      // atomicStore(p, v): release, `mov`
pub BI_ATOMIC_STORE_SC: long = 7;   // atomicStoreSeqCst(p, v): sequentially consistent, `xchg`
pub BI_ATOMIC_SWAP: long = 8;       // atomicSwap(p, v) -> long: the old value, `xchg`
pub BI_ATOMIC_CAS: long = 9;        // atomicCas(p, expected, desired) -> long: the old value, `lock cmpxchg`
pub BI_ATOMIC_ADD: long = 10;       // atomicAdd(p, delta) -> long: the old value, `lock xadd`
pub BI_ATOMIC_32: long = 6;         // added to each of the six for its `*int` form
pub isAtomicBuiltin bk:long -> bool { return bk >= BI_ATOMIC_LOAD && bk < BI_ATOMIC_LOAD + 2 * BI_ATOMIC_32; }
// The operation of an atomic builtin, as one of the six eight-byte kinds.
pub atomicOpOf bk:long -> long {
    if (bk >= BI_ATOMIC_LOAD + BI_ATOMIC_32) { return bk - BI_ATOMIC_32; }
    return bk;
}
// memcpy(dst, src, n): `n` bytes from `src` to `dst`, the two ranges apart; `rep movsb`, and a
// write of the destination range alone, which is all the optimizer takes it to end.
pub BI_MEMCPY: long = 17;
pub builtinOf f:FnNode -> long { return f.attrs >> BUILTIN_SHIFT; }
pub isNeverFn f:FnNode -> bool { return (f.attrs & FN_NEVER) != 0; }

// ─── the arena ───────────────────────────────────────────────────────────────

pub struct Ast {
    exprs:   Vec<Expr>,
    indexes: Vec<IndexNode>,
    calls:   Vec<CallNode>,
    fields:  Vec<FieldNode>,
    lits:    Vec<LitNode>,
    inits:   Vec<InitNode>,
    args:    Vec<NodeId>,        // every call's arguments, as runs

    stmts:   Vec<Stmt>,
    stmtPos: Vec<long>,          // beside `stmts`: where each statement stands (`posOf`)
    blocks:  Vec<Block>,
    stmtRuns: Vec<long>,         // every block's statements, as runs (indices into `stmts`)

    ifs:     Vec<IfNode>,
    whiles:  Vec<WhileNode>,
    returns: Vec<ReturnNode>,
    blockStmts: Vec<BlockStmtNode>,
    withs:   Vec<WithNode>,
    exprStmts: Vec<ExprStmtNode>,
    destructures: Vec<DestructureNode>,
    names:   Vec<Sym>,           // destructuring targets and match bindings, as runs
    arms:    Vec<ArmNode>,
    matches: Vec<MatchNode>,
    asms:    Vec<AsmNode>,
    asmPieces: Vec<AsmPiece>,
    decls:   Vec<VarDeclNode>,
    params:  Vec<long>,          // every function's parameters, as runs (indices into `decls`)
    fns:     Vec<FnNode>,
    structDecls: Vec<Sym>,

    images:  Vec<ImageNode>,
    imageBytes: Vec<u8>,         // every image's bytes, as runs
    relocs:  Vec<RelocNode>      // every image's pointer words, as runs
}

methods Ast for Default {
    new -> Ast {
        return Ast { exprs: vec![], indexes: vec![], calls: vec![], fields: vec![], lits: vec![], inits: vec![], args: vec![],
                     stmts: vec![], stmtPos: vec![], blocks: vec![], stmtRuns: vec![],
                     ifs: vec![], whiles: vec![], returns: vec![], blockStmts: vec![], withs: vec![], exprStmts: vec![],
                     destructures: vec![], names: vec![], arms: vec![], matches: vec![],
                     asms: vec![], asmPieces: vec![], decls: vec![], params: vec![],
                     fns: vec![], structDecls: vec![], images: vec![], imageBytes: vec![], relocs: vec![] };
    }
}

// How long every arena was at one moment: what a declaration the parser gives up on is cut back
// to (`Ast.rewindTo`). Every node the declaration made was appended after it.
pub struct AstMark {
    exprs: long, indexes: long, calls: long, fields: long, lits: long, inits: long, args: long,
    stmts: long, stmtPos: long, blocks: long, stmtRuns: long,
    ifs: long, whiles: long, returns: long, blockStmts: long, withs: long, exprStmts: long,
    destructures: long, names: long, arms: long, matches: long, asms: long, asmPieces: long,
    decls: long, params: long, fns: long, structDecls: long,
    images: long, imageBytes: long, relocs: long
}

methods Ast {
    mark &self -> AstMark {
        return AstMark { exprs: self.exprs.len(), indexes: self.indexes.len(), calls: self.calls.len(),
                         fields: self.fields.len(), lits: self.lits.len(), inits: self.inits.len(),
                         args: self.args.len(), stmts: self.stmts.len(), stmtPos: self.stmtPos.len(),
                         blocks: self.blocks.len(), stmtRuns: self.stmtRuns.len(), ifs: self.ifs.len(),
                         whiles: self.whiles.len(), returns: self.returns.len(),
                         blockStmts: self.blockStmts.len(), withs: self.withs.len(),
                         exprStmts: self.exprStmts.len(), destructures: self.destructures.len(),
                         names: self.names.len(), arms: self.arms.len(), matches: self.matches.len(),
                         asms: self.asms.len(), asmPieces: self.asmPieces.len(), decls: self.decls.len(),
                         params: self.params.len(), fns: self.fns.len(),
                         structDecls: self.structDecls.len(), images: self.images.len(),
                         imageBytes: self.imageBytes.len(), relocs: self.relocs.len() };
    }
    rewindTo &self m:AstMark -> void {
        self.exprs.truncate(m.exprs); self.indexes.truncate(m.indexes); self.calls.truncate(m.calls);
        self.fields.truncate(m.fields); self.lits.truncate(m.lits); self.inits.truncate(m.inits);
        self.args.truncate(m.args); self.stmts.truncate(m.stmts); self.stmtPos.truncate(m.stmtPos);
        self.blocks.truncate(m.blocks); self.stmtRuns.truncate(m.stmtRuns); self.ifs.truncate(m.ifs);
        self.whiles.truncate(m.whiles); self.returns.truncate(m.returns);
        self.blockStmts.truncate(m.blockStmts); self.withs.truncate(m.withs);
        self.exprStmts.truncate(m.exprStmts); self.destructures.truncate(m.destructures);
        self.names.truncate(m.names); self.arms.truncate(m.arms); self.matches.truncate(m.matches);
        self.asms.truncate(m.asms); self.asmPieces.truncate(m.asmPieces); self.decls.truncate(m.decls);
        self.params.truncate(m.params); self.fns.truncate(m.fns);
        self.structDecls.truncate(m.structDecls); self.images.truncate(m.images);
        self.imageBytes.truncate(m.imageBytes); self.relocs.truncate(m.relocs);
    }

    // ─── making nodes ────────────────────────────────────────────────────────

    addExpr &self e:Expr -> NodeId { self.exprs.push(e); return self.exprs.len() - 1; }
    expr &self id:NodeId -> Expr { return self.exprs.get(id); }
    setExpr &self id:NodeId e:Expr -> void { self.exprs.set(id, e); }

    // A binary operator over two finished operands. The result type is the wider of the two, which
    // is the one fact every arithmetic node needs and the only one decidable here.
    binary &self op:Op l:NodeId r:NodeId kind:Lit -> NodeId {
        return self.addExpr(Expr { op: op, left: l, right: r, kind: kind,
                                   structName: NO_SYM, isParen: false, payload: Payload.None });
    }

    // A node with one operand and no payload table of its own: a cast, a deref, a prefix operator.
    unary &self op:Op v:NodeId kind:Lit -> NodeId {
        return self.addExpr(Expr { op: op, left: NO_NODE, right: NO_NODE, kind: kind,
                                   structName: NO_SYM, isParen: false, payload: Payload.Sub(v) });
    }

    leaf &self op:Op p:Payload kind:Lit -> NodeId {
        return self.addExpr(Expr { op: op, left: NO_NODE, right: NO_NODE, kind: kind,
                                   structName: NO_SYM, isParen: false, payload: p });
    }

    // The same, for a kind whose meaning needs its companion name: a struct, a trait object.
    leafOf &self op:Op p:Payload kind:Lit name:Sym -> NodeId {
        return self.addExpr(Expr { op: op, left: NO_NODE, right: NO_NODE, kind: kind,
                                   structName: name, isParen: false, payload: p });
    }

    // `sizeof(T)`: a `long`, whose operand is a bare leaf carrying T as its own type. The type
    // measured rides on a node of its own so that nothing reading the expression's type (an
    // operator's rule, a store, an argument, a `...any` box) ever mistakes the count for a T.
    // Monomorphization substitutes the leaf like any node; `measuredOf` reads it.
    sizeofNode &self kind:Lit name:Sym -> NodeId {
        t: NodeId = self.leafOf(Op.Literal, Payload.None, kind, name);
        return self.addExpr(Expr { op: Op.Sizeof, left: NO_NODE, right: NO_NODE, kind: Lit.Long,
                                   structName: NO_SYM, isParen: false, payload: Payload.Sub(t) });
    }
    measuredOf &self id:NodeId -> Expr {
        p: Payload = self.expr(id).payload;
        match p { Sub(t) { return self.expr(t); } _ { } }
        return self.expr(id);
    }

    // ─── runs ────────────────────────────────────────────────────────────────
    // Each of these takes a finished local vector and appends it as one contiguous block, which is
    // what keeps a run's elements together while the recursion that built them appended others'.

    addArgs &self ids:Vec<NodeId> -> long {
        first: long = self.args.len();
        self.args.extend(ids);
        return first;
    }
    argAt &self c:CallNode k:long -> NodeId { return self.args.get(c.firstArg + k); }

    addInits &self ids:Vec<InitNode> -> long {
        first: long = self.inits.len();
        self.inits.extend(ids);
        return first;
    }

    addBlock &self ids:Vec<long> -> long {
        first: long = self.stmtRuns.len();
        self.stmtRuns.extend(ids);
        self.blocks.push(Block { firstStmt: first, stmtCount: ids.len() });
        return self.blocks.len() - 1;
    }
    // A negative block id is the absence of a body: a function `pub`-declared here and defined
    // in another object. It reads as an empty block, so every walk over one does nothing without
    // each of the twenty-odd callers having to ask. Guarding here rather than at the call sites
    // is what makes that true for the next walker somebody writes, too.
    blockLen &self b:long -> long {
        if (b < 0) { return 0; }
        return self.blocks.get(b).stmtCount;
    }
    stmtAt &self b:long k:long -> Stmt {
        return self.stmts.get(self.stmtIdAt(b, k));
    }
    // The statement's ID rather than the statement, which is what a caller rebuilding a block
    // with more statements in front of it needs: a match arm's payload bindings.
    stmtIdAt &self b:long k:long -> long {
        return self.stmtRuns.get(self.blocks.get(b).firstStmt + k);
    }

    addNames &self ids:Vec<Sym> -> long {
        first: long = self.names.len();
        self.names.extend(ids);
        return first;
    }
    addParams &self ids:Vec<long> -> long {
        first: long = self.params.len();
        self.params.extend(ids);
        return first;
    }
    paramAt &self f:FnNode k:long -> VarDeclNode {
        return self.decls.get(self.params.get(f.firstArg + k));
    }

    // ─── statements ──────────────────────────────────────────────────────────

    // A statement stands where the compiler is working (`gPos`): the parser has set that to the
    // statement being read, and a later pass to the statement it is rewriting.
    addStmt &self k:StmtKind at:long -> long {
        self.stmts.push(Stmt { kind: k, at: at });
        self.stmtPos.push(gPos);
        return self.stmts.len() - 1;
    }
    // Makes statement `id` the current position, so an error from here on points at it, and
    // returns the previous position for the caller to restore once it is done with the statement.
    // A statement with no position of its own leaves the enclosing one's in force.
    enterStmt &self id:long -> long {
        was: long = gPos;
        p: long = self.stmtPos.get(id);
        if (p != 0) { gPos = p; }
        return was;
    }
}

// ─── the arenas, by name, and moving a node between trees ────────────────────
// A `.klib` carries a module's tree as small dense trees of its own (`1-cumulation/KlibTree.k`):
// the module's declarations, and each function body apart. Writing one copies nodes out of the
// program's tree (a graft); reading one shifts every index by where the arena it points into
// starts in the reader's tree (a rebase). Both are the same walk over a node's index fields, so
// each node type lists its index fields once, below (`mapExpr` and the rest), and an `IdMap` says
// what an index becomes. A negative index (`NO_NODE`, a missing `else`, a body that is not there)
// is never one, and passes through as it is.

pub enum Arena: int {
    Exprs, Indexes, Calls, Fields, Lits, Inits, Args,
    Stmts, Blocks, StmtRuns,
    Ifs, Whiles, Returns, BlockStmts, Withs, ExprStmts, Destructures, Names,
    Arms, Matches, Asms, AsmPieces, Decls, Params, Fns, StructDecls,
    // Not the tree's: the registry's runs of bounds, which a function names (`firstBound`).
    Bounds,
    // A statement that points nowhere (`break`, `continue`).
    Nowhere
}

// What an index into `arena` becomes (`id`), and where a run of `count` elements starting at
// `first` ends up (`run`). `src` is the tree being read from, which only a graft needs.
pub trait IdMap {
    id &self src:Ast arena:Arena v:long -> long;
    run &self src:Ast arena:Arena first:long count:long -> long;
}

// Which side table a statement's `at` indexes, by its kind.
pub stmtArena k:StmtKind -> Arena {
    if (k == StmtKind.FunctionDef) { return Arena.Fns; }
    if (k == StmtKind.VarDecl) { return Arena.Decls; }
    if (k == StmtKind.If) { return Arena.Ifs; }
    if (k == StmtKind.Loop || k == StmtKind.Unsafe || k == StmtKind.Block) { return Arena.BlockStmts; }
    if (k == StmtKind.While || k == StmtKind.Recover) { return Arena.Whiles; }
    if (k == StmtKind.With) { return Arena.Withs; }
    if (k == StmtKind.Return) { return Arena.Returns; }
    if (k == StmtKind.Call || k == StmtKind.Expr) { return Arena.ExprStmts; }
    if (k == StmtKind.Asm) { return Arena.Asms; }
    if (k == StmtKind.Destructure) { return Arena.Destructures; }
    if (k == StmtKind.Match) { return Arena.Matches; }
    if (k == StmtKind.StructDecl) { return Arena.StructDecls; }
    return Arena.Nowhere;
}

pub mapExpr<M: IdMap> x:Expr inout m:M src:Ast -> Expr {
    p: Payload = x.payload;
    match x.payload {
        Index(i) { p = Payload.Index(m.id(src, Arena.Indexes, i)); }
        Call(i)  { p = Payload.Call(m.id(src, Arena.Calls, i)); }
        Field(i) { p = Payload.Field(m.id(src, Arena.Fields, i)); }
        Lit(i)   { p = Payload.Lit(m.id(src, Arena.Lits, i)); }
        Sub(i)   { p = Payload.Sub(m.id(src, Arena.Exprs, i)); }
        _ { }
    }
    return Expr { op: x.op, left: m.id(src, Arena.Exprs, x.left), right: m.id(src, Arena.Exprs, x.right),
                  kind: x.kind, structName: x.structName, isParen: x.isParen, payload: p };
}
pub mapIndex<M: IdMap> x:IndexNode inout m:M src:Ast -> IndexNode {
    return IndexNode { name: x.name, base: m.id(src, Arena.Exprs, x.base), index: m.id(src, Arena.Exprs, x.index),
                       whole: x.whole, rawPointerBase: x.rawPointerBase,
                       sliceStart: m.id(src, Arena.Exprs, x.sliceStart), sliceEnd: m.id(src, Arena.Exprs, x.sliceEnd),
                       at: x.at };
}
pub mapCall<M: IdMap> x:CallNode inout m:M src:Ast -> CallNode {
    return CallNode { name: x.name, receiver: m.id(src, Arena.Exprs, x.receiver),
                      firstArg: m.run(src, Arena.Args, x.firstArg, x.argCount), argCount: x.argCount,
                      slot: x.slot, callee: m.id(src, Arena.Exprs, x.callee), sigKey: x.sigKey };
}
pub mapField<M: IdMap> x:FieldNode inout m:M src:Ast -> FieldNode {
    return FieldNode { base: m.id(src, Arena.Exprs, x.base), name: x.name };
}
pub mapLit<M: IdMap> x:LitNode inout m:M src:Ast -> LitNode {
    return LitNode { typeName: x.typeName, firstInit: m.run(src, Arena.Inits, x.firstInit, x.initCount),
                     initCount: x.initCount, rest: m.id(src, Arena.Exprs, x.rest) };
}
pub mapInit<M: IdMap> x:InitNode inout m:M src:Ast -> InitNode {
    return InitNode { name: x.name, value: m.id(src, Arena.Exprs, x.value) };
}
pub mapStmt<M: IdMap> x:Stmt inout m:M src:Ast -> Stmt {
    ar: Arena = stmtArena(x.kind);
    if (ar == Arena.Nowhere) { return x; }
    return Stmt { kind: x.kind, at: m.id(src, ar, x.at) };
}
pub mapBlock<M: IdMap> x:Block inout m:M src:Ast -> Block {
    return Block { firstStmt: m.run(src, Arena.StmtRuns, x.firstStmt, x.stmtCount), stmtCount: x.stmtCount };
}
pub mapIf<M: IdMap> x:IfNode inout m:M src:Ast -> IfNode {
    return IfNode { cond: m.id(src, Arena.Exprs, x.cond), body: m.id(src, Arena.Blocks, x.body),
                    elseIf: m.id(src, Arena.Ifs, x.elseIf) };
}
pub mapWhile<M: IdMap> x:WhileNode inout m:M src:Ast -> WhileNode {
    return WhileNode { cond: m.id(src, Arena.Exprs, x.cond), body: m.id(src, Arena.Blocks, x.body),
                       step: m.id(src, Arena.Blocks, x.step) };
}
pub mapReturn<M: IdMap> x:ReturnNode inout m:M src:Ast -> ReturnNode {
    return ReturnNode { value: m.id(src, Arena.Exprs, x.value) };
}
pub mapBlockStmt<M: IdMap> x:BlockStmtNode inout m:M src:Ast -> BlockStmtNode {
    return BlockStmtNode { body: m.id(src, Arena.Blocks, x.body) };
}
pub mapWith<M: IdMap> x:WithNode inout m:M src:Ast -> WithNode {
    return WithNode { name: x.name, body: m.id(src, Arena.Blocks, x.body) };
}
pub mapExprStmt<M: IdMap> x:ExprStmtNode inout m:M src:Ast -> ExprStmtNode {
    return ExprStmtNode { value: m.id(src, Arena.Exprs, x.value) };
}
pub mapDestructure<M: IdMap> x:DestructureNode inout m:M src:Ast -> DestructureNode {
    return DestructureNode { firstName: m.run(src, Arena.Names, x.firstName, x.nameCount), nameCount: x.nameCount,
                             value: m.id(src, Arena.Exprs, x.value) };
}
pub mapArm<M: IdMap> x:ArmNode inout m:M src:Ast -> ArmNode {
    return ArmNode { variant: x.variant, test: m.id(src, Arena.Exprs, x.test),
                     firstBind: m.run(src, Arena.Names, x.firstBind, x.bindCount), bindCount: x.bindCount,
                     body: m.id(src, Arena.Blocks, x.body) };
}
pub mapMatch<M: IdMap> x:MatchNode inout m:M src:Ast -> MatchNode {
    return MatchNode { scrutinee: x.scrutinee, firstArm: m.run(src, Arena.Arms, x.firstArm, x.armCount),
                       armCount: x.armCount };
}
pub mapAsm<M: IdMap> x:AsmNode inout m:M src:Ast -> AsmNode {
    return AsmNode { firstPiece: m.run(src, Arena.AsmPieces, x.firstPiece, x.pieceCount), pieceCount: x.pieceCount,
                     noReturn: x.noReturn };
}
pub mapAsmPiece<M: IdMap> x:AsmPiece inout m:M src:Ast -> AsmPiece {
    return AsmPiece { kind: x.kind, reg: x.reg, name: x.name, value: m.id(src, Arena.Exprs, x.value), text: x.text };
}
pub mapDecl<M: IdMap> x:VarDeclNode inout m:M src:Ast -> VarDeclNode {
    return VarDeclNode { name: x.name, kind: x.kind, structName: x.structName, isArray: x.isArray, count: x.count,
                         conv: x.conv, isVariadic: x.isVariadic, elemKind: x.elemKind, elemStruct: x.elemStruct,
                         init: m.id(src, Arena.Exprs, x.init) };
}
// A function's bounds are the registry's, and only a function that has some points at any.
pub mapFn<M: IdMap> x:FnNode inout m:M src:Ast -> FnNode {
    fb: long = 0;
    if (x.boundCount > 0) { fb = m.id(src, Arena.Bounds, x.firstBound); }
    return FnNode { name: x.name, returnKind: x.returnKind, returnStruct: x.returnStruct, visibility: x.visibility,
                    file: x.file, pkg: x.pkg, isUnsafe: x.isUnsafe, isTemplate: x.isTemplate,
                    firstBound: fb, boundCount: x.boundCount,
                    firstArg: m.run(src, Arena.Params, x.firstArg, x.argCount), argCount: x.argCount,
                    body: m.id(src, Arena.Blocks, x.body), inferReturn: x.inferReturn, attrs: x.attrs };
}

// The enums a tree is made of decode with a range check. Every value from the first variant to
// the last is a variant (none of these enums skips a value), whereas the derived decoder would
// compare against each one in turn.
local NO_VARIANT: str = "a value the enum has no variant for";
methods Op for Decode {
    decode inp:&Decoder -> Op {
        v: long = inp.getVarint();
        if (v < 0 || v > Op.ArrayLit as long) { inp.fail(NO_VARIANT); v = 0; }
        return v as Op;
    }
}
methods Lit for Decode {
    decode inp:&Decoder -> Lit {
        v: long = inp.getVarint();
        if (v < 0 || v > Lit.Len as long) { inp.fail(NO_VARIANT); v = 0; }
        return v as Lit;
    }
}
methods StmtKind for Decode {
    decode inp:&Decoder -> StmtKind {
        v: long = inp.getVarint();
        if (v < 0 || v > StmtKind.Recover as long) { inp.fail(NO_VARIANT); v = 0; }
        return v as StmtKind;
    }
}
methods Conv for Decode {
    decode inp:&Decoder -> Conv {
        v: long = inp.getVarint();
        if (v < 0 || v > Conv.Sink as long) { inp.fail(NO_VARIANT); v = 0; }
        return v as Conv;
    }
}
methods Vis for Decode {
    decode inp:&Decoder -> Vis {
        v: long = inp.getVarint();
        if (v < 0 || v > Vis.Pub as long) { inp.fail(NO_VARIANT); v = 0; }
        return v as Vis;
    }
}
methods AsmKind for Decode {
    decode inp:&Decoder -> AsmKind {
        v: long = inp.getVarint();
        if (v < 0 || v > AsmKind.Text as long) { inp.fail(NO_VARIANT); v = 0; }
        return v as AsmKind;
    }
}
methods RelocKind for Decode {
    decode inp:&Decoder -> RelocKind {
        v: long = inp.getVarint();
        if (v < 0 || v > RelocKind.Fn as long) { inp.fail(NO_VARIANT); v = 0; }
        return v as RelocKind;
    }
}

// ─── lengths ─────────────────────────────────────────────────────────────────
//
// `struct Buf<N: long> { data: [u8; N] }`: a template may take a length, which stands where an
// array's length does and, in a body, for its value. An array's length is a `count: long`
// wherever one is recorded (a field, a declaration, a global), so inside a template a length that
// is still a parameter is recorded in the same place, as a negative number naming the parameter:
// no real length is negative, and each instance writes the value over it when it is stamped.
pub countOfParam p:Sym -> long { return -1 - (p as long); }
pub isParamCount c:long -> bool { return c < 0; }
pub paramOfCount c:long -> Sym { return (-1 - c) as Sym; }

// A length as a `.klib` writes it. The name a parameter's length holds is an interned index, which
// means nothing in another process, so a parameter goes as its name's place in the string table,
// negative: -1 is the first name.
pub putCount out:&Encoder c:long -> void {
    if (!isParamCount(c)) { out.putVarint(c); return; }
    out.putVarint(-1 - symOut(paramOfCount(c)));
}
pub getCount inp:&Decoder -> long {
    v: long = inp.getVarint();
    if (v >= 0) { return v; }
    return countOfParam(symAt(inp, -v));
}

// A declaration carries a length, so its codec is written out rather than derived.
methods VarDeclNode for Encode {
    encode &self out:&Encoder -> void {
        self.name.encode(out); self.kind.encode(out); self.structName.encode(out); self.isArray.encode(out);
        putCount(out, self.count);
        self.conv.encode(out); self.isVariadic.encode(out); self.elemKind.encode(out);
        self.elemStruct.encode(out); out.putVarint(self.init);
    }
}
methods VarDeclNode for Decode {
    decode inp:&Decoder -> VarDeclNode {
        name: Sym = Sym.decode(inp);
        kind: Lit = Lit.decode(inp);
        sn: Sym = Sym.decode(inp);
        isArray: bool = bool.decode(inp);
        count: long = getCount(inp);
        conv: Conv = Conv.decode(inp);
        isVariadic: bool = bool.decode(inp);
        ek: Lit = Lit.decode(inp);
        es: Sym = Sym.decode(inp);
        return VarDeclNode { name: name, kind: kind, structName: sn, isArray: isArray, count: count, conv: conv,
                             isVariadic: isVariadic, elemKind: ek, elemStruct: es, init: inp.getVarint() };
    }
}

// A function's `body`: a block, or one of these. A function declared and not defined has none;
// a dependency's function whose body is still in its `.klib` has one that has not been read
// (`treecodec.ensureBody` reads it); a generic instance's method another package compiled, or
// one nothing here has reached yet, has one not yet stamped (`Mono.stampBody`). Each reads as an
// empty block (`blockLen`).
pub NO_BODY: long = -1;
pub BODY_LAZY: long = -2;
pub BODY_STAMP: long = -3;
pub hasBody f:FnNode -> bool { return f.body >= 0 || f.body == BODY_LAZY || f.body == BODY_STAMP; }

// `*r` where `r` is a borrow (`Lit.Ref`): the place the borrow lends, not a raw pointer's target.
// The checker writes one for a store to a lent place as a whole (`p = v` with `inout p`, `self = v`
// in a `&self` method; `Checker.lendWhole`), so the store writes the caller's value; every pass
// that follows a place to its root goes through one as it goes through a field. Returns `r`'s
// node, or NO_NODE for anything else, a raw pointer's `*p` included.
pub lentPlaceOf inout a:Ast id:NodeId -> NodeId {
    if (id == NO_NODE) { return NO_NODE; }
    e: Expr = a.expr(id);
    if (e.op != Op.Deref) { return NO_NODE; }
    v: NodeId = NO_NODE;
    match e.payload { Sub(x) { v = x; } _ { } }
    if (v == NO_NODE || a.expr(v).kind != Lit.Ref) { return NO_NODE; }
    return v;
}

// The hidden element pointer of a `for x in xs` (`Parser.parseForEach`) that `id` names: `$forpK`
// in the plain form, `$forwK` where the loop lends `xs` (`for x in &xs`). NO_SYM for anything else.
// The checker trusts an index through one, turns a struct element into a borrow of it
// (`Checker.bmForLoop`), and the guard holds the loop's body to what the loop lends
// (`ConstGuard.holdLoop`).
pub forPointerOf inout a:Ast id:NodeId -> Sym {
    if (id == NO_NODE) { return NO_SYM; }
    e: Expr = a.expr(id);
    if (e.op != Op.Lvalue) { return NO_SYM; }
    match e.payload {
        Name(n) {
            s: str = nameOf(n);
            if (s.len > 5 && charAt(s, 0) == '$' && charAt(s, 1) == 'f' && charAt(s, 2) == 'o'
                && charAt(s, 3) == 'r' && (charAt(s, 4) == 'p' || charAt(s, 4) == 'w')) { return n; }
        }
        _ { }
    }
    return NO_SYM;
}
pub forLends n:Sym -> bool { return charAt(nameOf(n), 4) == 'w'; }

// The hidden pointer of a `for x in xs` whose body is `b`, or NO_SYM when `b` is not one: the
// parser's `x: T; x = $forpK[$foriK];` (`x = &$forpK[$foriK]` once a struct element is a borrow)
// at the head of the body. The loop variable is the first statement's declaration.
pub forLoopPtr inout a:Ast b:long -> Sym {
    if (b < 0 || a.blockLen(b) < 2) { return NO_SYM; }
    ds: Stmt = a.stmtAt(b, 0);
    ss: Stmt = a.stmtAt(b, 1);
    if (ds.kind != StmtKind.VarDecl || ss.kind != StmtKind.Expr) { return NO_SYM; }
    e: Expr = a.expr(a.exprStmts.get(ss.at).value);
    if (e.op != Op.Assignment || e.right == NO_NODE) { return NO_SYM; }
    at: NodeId = e.right;
    r: Expr = a.expr(at);
    if (r.op == Op.AddressOf) { match r.payload { Sub(v) { at = v; } _ { } } }
    r = a.expr(at);
    p: Sym = NO_SYM;
    match r.payload { Index(i) { p = forPointerOf(a, a.indexes.get(i).base); } _ { } }
    return p;
}
