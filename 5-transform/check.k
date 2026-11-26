// Typing the tree.
//
// The parser records what syntax alone can decide. Everything else (what a call returns, what a
// field holds, where two operands meet) needs the declarations, and that is what this pass adds:
// one walk per function, a type stamped on every expression, and a refusal for what does not fit.
#include <parse::{ast, astdump, parser, registry, types, quoter, treecodec, diag}>
#include <eval>
#include <mono>         // a generic type's conditional impl, stamped once a derive meets its bounds
#include <parse::upstream>
#include <facts>
#include <support::{compiler, imports}>
#include <stdlib::{fmt, option, string, vec, path}>

// What a name means here: its type, the aggregate it names when it has one, and whether it is an
// array of that type rather than one of it. The array bit matters because `xs[i]` yields the
// element while `xs` itself is the whole block: without it, indexing an array of structs scales
// by the wrong width, silently.
pub struct VarType { kind: Lit, structName: Sym, isArray: bool }

pub varType k:Lit n:Sym -> VarType { return VarType { kind: k, structName: n, isArray: false }; }

// Turns a mangled type name back into a type. `*T` and `[T]` record their element this way, so
// binding one to a parameter means reading the spelling as the type it stands for. A `fn(...)->R`
// records only its return like this; anything that needs the parameters reads the declaration.
pub typeRefNamed n:str -> TypeRef {
    if (namesScalar(n)) { return TypeRef { base: scalarNamed(n), name: NO_SYM }; }
    return TypeRef { base: Lit.Struct, name: intern(n) };
}

// An implementation stubbed for a derive: of `trait` for `owner`, which `requester` (the function
// being checked, NO_SYM for a global) needed. Written when the trait's macro can run.
pub struct DeriveJob { owner: Sym, trait: Sym, requester: Sym, pos: long }   // pos: where it was needed

// One value a scope must release: the variable, the type whose `drop` releases it, and the
// element count when it is an array of them (0 for a single value).
pub struct OwnLocal { name: Sym, structName: Sym, count: long }

// What a store has to release: whether there is an old value at all, whose flag says it was
// live (NO_SYM when the place is always live), and the type whose `drop` releases it.
pub struct StoreDrop { needed: bool, guard: Sym, structName: Sym }

// A write of a partial move's flag that may turn out not to be needed: an empty block written
// where the store would go (`at` indexes `blockStmts`), filled once the function is walked if the
// move `entry` got a flag. `value` is what the store writes: 1 at the move, 0 where it is undone.
pub struct PHole { at: long, entry: Sym, value: long }

// One aggregate argument's access during a call: where its path sits in the flattened table of
// path components, how long it is, and whether the call may write through it.
pub struct Access { first: long, count: long, writes: bool }

// What a body does to a parameter: writes it or lets raw code at it, and hands its value on.
// Only the first refuses a borrow outright; the second does so for a type that owns something.
local CONV_FORCED: long = 1;
local CONV_GIVEN:  long = 2;

// Convention inference is a monotone demotion, so it settles; the bound is a guard against a
// mistake in that argument, not a real depth.
local MAX_CONV_ROUNDS: long = 8;

// How deep a chain of "this one never returns either" can be. A trap wrapped in a wrapper is
// two; nothing in the standard library is more than that.
local MAX_DIVERGE_ROUNDS: long = 8;

// How far to follow a struct's fields looking for a borrowed view. A self-referential type would
// otherwise walk forever; nothing real nests a closure more than a couple of levels down.
local MAX_VIEW_DEPTH: long = 8;

// An untyped integer literal: `2` rather than a typed local. Its type is a default, not a fact:
// it widens to whatever it is compared against, so it is the one kind of argument that is allowed
// to lose an argument when a generic call's type parameters are inferred.
pub isWeakLiteral e:Expr -> bool {
    if (e.op != Op.Literal) { return false; }
    return e.kind == Lit.Int || e.kind == Lit.Long || e.kind == Lit.Char;
}

// The condition the parser writes for a bare `else`: the literal `true`. Recognising it is what
// tells an if-chain that ends in one from a chain that can fall past its last branch.
pub isAlwaysTrue e:Expr -> bool {
    if (e.op != Op.Literal || e.kind != Lit.Bool) { return false; }
    p: Payload = e.payload;
    match p { Num(v) { return v != 0; } _ { } }
    return false;
}

// The program's `@panic` function, found once (`Checker.panicTarget`).
local var gPanicFn: Sym = NO_SYM;
local var gPanicScanned: bool = false;
// The program's `@recover` function, found once (`Checker.recoverTarget`): what the code a `recover`
// statement is lowered to calls to link and unlink its record.
pub var gRecoverFn: Sym = NO_SYM;
local var gRecoverScanned: bool = false;

// A concrete value that a trait-typed parameter can be built from. A borrow is one: a trait
// object is {data, vtable} and a ref is already the data pointer, so the coercion costs nothing
// the by-value one did not, which is what lets a function that was lent a `String` write into it
// through `Write`. The lowerer builds the pair the same way for both.
pub isConcreteForTrait e:Expr -> bool {
    if (e.structName == NO_SYM) { return false; }
    return e.kind == Lit.Struct || e.kind == Lit.Ref;
}

pub namedType n:Sym -> VarType {
    if (n == NO_SYM) { return varType(Lit.Void, NO_SYM); }
    if (namesScalar(nameOf(n))) { return varType(scalarNamed(nameOf(n)), NO_SYM); }
    return varType(Lit.Struct, n);
}

// A struct's members, for the diagnostic that says a name is not one of them: "fields `x`, `y`",
// or "no fields". The compiler's own fields are skipped: a sum type's `$tag` and its per-variant
// payload slots are laid out by the parser and nobody writes them, so naming them back would send
// the reader looking for a member their source does not contain.
pub fieldNamesOf d:StructDef -> str {
    s: String;
    s.pushStr("fields `");
    n: long = 0;
    // A tuple's elements are its fields `$0`, `$1`, written `t.0`, `t.1`.
    tuple: bool = isTupleName(d.name);
    for k in 0..d.fieldCount {
        f: str = nameOf(gReg.fieldAt(d, k).name);
        if (f.len > 0 && charAt(f, 0) == '$') {
            if (!tuple) { continue; }
            f = strSlice(f, 1, f.len - 1);
        }
        if (n > 0) { s.pushStr("`, `"); }
        s.pushStr(f);
        n = n + 1;
    }
    if (n == 0) { return "no fields"; }
    s.push('`');
    return keepString(s);
}

// A kind with no fields whatever its companion name: the scalars, `any`, a function pointer, an
// untyped raw pointer. A struct, a borrow or a trait object without a name is a type the checker
// lost track of, which is not this question.
local fieldless k:Lit -> bool {
    return k == Lit.Int || k == Lit.Long || k == Lit.Char || k == Lit.Float || k == Lit.Double
        || k == Lit.I16 || k == Lit.U8 || k == Lit.U16 || k == Lit.U32 || k == Lit.U64
        || k == Lit.Bool || k == Lit.Any || k == Lit.Fn || k == Lit.Ptr;
}

// What a call through a `fn` value yields. A fn type's companion is a key into the signature
// table rather than a type name of its own, so the result is looked up there and never read off
// the spelling.
pub fnSigReturn key:Sym -> VarType {
    at: long = gFnSigs.find(key);
    if (at < 0) { return varType(Lit.Void, NO_SYM); }
    r: TypeRef = gFnSigs.sigAt(at).ret;
    return varType(r.base, r.name);
}

// What a `...any` run can carry, which is exactly what `Lowerer::boxAny` knows how to build a
// box from. A type still being decided answers yes: this runs while instances are being stamped.
pub boxableAsAny k:Lit n:Sym -> bool {
    if (isInteger(k) || k == Lit.Bool || k == Lit.Ptr || k == Lit.Str) { return true; }
    if (k == Lit.Float || k == Lit.Double) { return true; }
    if (k == Lit.TypeVar || k == Lit.Void || k == Lit.Any) { return true; }
    if (isBackedEnum(n)) { return true; }
    if (k == Lit.TraitObj) { return n != NO_SYM && lastComponentOf(nameOf(n)) == "Display"; }
    if (k == Lit.Struct || k == Lit.Ref) {
        return n != NO_SYM && gReg.structImplements(nameOf(n), intern("Display"));
    }
    return false;
}

// Whether `n` names an enum whose variants carry nothing: a set of integer constants, whose
// values are integers of the backing width. A sum type answers no: it is laid out as a struct.
pub isBackedEnum n:Sym -> bool {
    if (n == NO_SYM) { return false; }
    at: long = gReg.findEnumSym(n);
    if (at < 0) { return false; }
    return !gReg.enumDef(at).hasPayload;
}

// The value a borrow of a scalar or a `str` is, or `Lit.Void` when `t` is no such borrow. Only a
// `&self` of `methods long`, `methods str`... has this type (`inout` takes no scalar, and a
// stamped `&T` at a scalar T is the scalar), and it receives the value itself.
pub scalarRefKind t:VarType -> Lit {
    if (t.kind != Lit.Ref || t.structName == NO_SYM || t.isArray) { return Lit.Void; }
    q: str = nameOf(t.structName);
    if (!namesScalar(q)) { return Lit.Void; }
    k: Lit = scalarNamed(q);
    if (isInteger(k) || k == Lit.Bool || k == Lit.Char || k == Lit.Float || k == Lit.Double || k == Lit.Str) { return k; }
    return Lit.Void;
}

// Whether a value of kind `gk` (companion name `gn`) may be handed to a place of kind `wk`
// (companion `wn`). `weak` says the value is an untyped literal, which takes the type it is
// handed rather than carrying one.
//
// It is permissive wherever the compiler does not know a type yet (an unstamped type parameter,
// a call whose return is still being decided, `any`), because this runs during the rounds where
// those are being settled, and a refusal invented from a half-known type is worse than saying
// nothing. What it does catch is a mismatch of category: a `str` is a {ptr,len} pair and a
// `long` is a word, and handing either where the other is declared reads sixteen bytes off an
// eight-byte slot. The scalar rule itself is `canImplicitlyConvert` (`parse::types`).
pub typeFits wk0:Lit wn0:Sym gk0:Lit gn0:Sym weak:bool -> bool {
    // A borrow of a scalar is the scalar: `&u64` and `u64` are one argument, and which of the
    // two a stamped generic parameter is written as depends on the pass that retyped it.
    wk: Lit = wk0; wn: Sym = wn0; gk: Lit = gk0; gn: Sym = gn0;
    if (wk == Lit.Ref && wn != NO_SYM && namesScalar(nameOf(wn))) {
        wk = scalarNamed(nameOf(wn)); wn = NO_SYM;
    }
    if (gk == Lit.Ref && gn != NO_SYM && namesScalar(nameOf(gn))) {
        gk = scalarNamed(nameOf(gn)); gn = NO_SYM;
    }
    if (wk == gk && (wn == gn || wn == NO_SYM || gn == NO_SYM)) { return true; }
    if (wk == Lit.Void || gk == Lit.Void) { return true; }
    if (wk == Lit.TypeVar || gk == Lit.TypeVar) { return true; }
    if (wk == Lit.Any || gk == Lit.Any) { return true; }
    // A concrete value becomes a trait object where one is wanted; `boxTraitArgs` builds the
    // {data, vtable} pair. A scalar cannot (it has no vtable) but that is its own diagnostic.
    if (wk == Lit.TraitObj) {
        return gk == Lit.Struct || gk == Lit.Ref || gk == Lit.TraitObj || gk == Lit.Ptr;
    }
    // A backed enum is an integer that remembers which enum it came from: `Access.Read` types as
    // the backing width, and the parameter that takes it names the enum. A sum type is not one
    // of these (it is laid out as a struct), so the test is `hasPayload`. Neither is a distinct
    // type, which converts only with `as`.
    if (isBackedEnum(wn) && !gReg.isDistinct(wn) && (isInteger(gk) || (isBackedEnum(gn) && !gReg.isDistinct(gn)))) { return true; }
    if (isBackedEnum(gn) && !gReg.isDistinct(gn) && isInteger(wk)) { return true; }
    // A struct and a borrow of one are the same argument. A name mismatch between two structs is
    // reported where it can name both, so it is not refused here.
    if (wk == Lit.Struct || wk == Lit.Ref) {
        return gk == Lit.Struct || gk == Lit.Ref || gk == Lit.Ptr;
    }
    if (wk == Lit.Fn && gk == Lit.Fn) { return fnSigsFit(wn, gn); }
    if (wk == Lit.Fn)    { return gk == Lit.Ptr || gk == Lit.Long; }
    if (wk == Lit.Slice) { return gk == Lit.Slice || gk == Lit.Str || gk == Lit.Ptr; }
    if (wk == Lit.Str)   { return gk == Lit.Str || gk == Lit.Slice; }
    if (wk == Lit.Tuple) { return gk == Lit.Tuple; }
    // A raw pointer is an address, and `unsafe` code builds one from whatever holds it.
    if (wk == Lit.Ptr)   { return gk == Lit.Ptr || gk == Lit.Ref || isInteger(gk); }
    // An untyped literal takes the width it is handed: `f(3)` into a `u8` parameter is a 3, not
    // a narrowing the author has to write out.
    // Not into a float: `x: f64 = 3` is refused, `3.0` or `3 as f64` is what is meant.
    if (weak && (isInteger(wk) || wk == Lit.Bool)) {
        return isInteger(gk) || gk == Lit.Bool;
    }
    return canImplicitlyConvert(gk, wk);
}

// How many arguments that signature takes, or -1 when the key names no signature, which is not
// an error here: an unknown key means there is nothing to hold the call to, and the ordinary
// unresolved-name diagnostics say more than a made-up arity would.
pub fnSigArity key:Sym -> long {
    at: long = gFnSigs.find(key);
    if (at < 0) { return -1; }
    return gFnSigs.sigAt(at).paramCount;
}

// Holds only the tables it builds. The tree is borrowed per call and never owned: a Checker
// built from a borrow would be moving a tree that belongs to the caller.
pub struct Checker {
    vars: HashMap<str, long>,      // local or global name -> index into `types`
    types: Vec<VarType>,
    fnReturns: HashMap<str, long>, // function name -> index into `types`
    fnNames:   HashMap<str, Sym>,  // and the qualified name it resolves to
    varNames:  HashMap<str, Sym>,  // a bare global name -> the qualified one it declares
    locals:    HashMap<str, bool>, // what the function being checked declared, so a local that
                                   // happens to share a global's bare name still wins
    fnAt:      HashMap<str, long>, // function name -> its node, for reading parameter types
    privateIn: HashMap<str, Sym>,  // a file-private function -> its file: no other file's candidate
    // Every function by its bare component, so a bare call finds its candidates directly instead
    // of asking, module by module, whether each one declares the name.
    fnBare:    BareIndex,
    // The functions that never come back, grown to a fixpoint by `checkReturns`. Seeded from the
    // declarations (`-> never`, and a dependency's facts); this holds what they reach.
    diverging: HashMap<str, bool>,
    // Generic functions this pass called and monomorphization has not stamped yet. A call is
    // what instantiates one, and only here are the argument types known.
    wanted: Vec<FnRequest>,
    // Structs whose `Clone` has to be derived, for the same reason and by the same round trip.
    wantedClones: Vec<Sym>,
    addrOperand: NodeId,           // the operand of the `&` being checked: `&f` names a function
    ownUnsafe: long,               // the ownership walk is inside `unsafe`
    addrFills: Vec<Sym>,           // owning locals whose raw address the current statement takes
    stmtMoves: long,               // moves the ownership walk has made in the current statement
    globalFnRefs: Vec<NodeId>,     // every `&f` in a global's initializer, for `enforceFnRef`
    globalFnRefPos: Vec<long>,     // and where it stands
    guards: long,                 // makes each `with`'s guard a distinct name
    // The `hold()` calls a `with` statement makes (by their index in `calls`): trusted whether or
    // not the method is declared `unsafe`, since the guard it returns lives exactly for the block,
    // inside the borrow it keeps a pointer into.
    withHolds: HashMap<long, bool>,
    currentReturn: VarType,
    currentModule: Sym,            // the module whose body is being checked, for bare names
    // The file and package the body being checked was written in: what `local` and `pkg` are
    // measured against. NO_SYM where there is no answer, and then nothing is enforced.
    currentFile: Sym,
    currentPkg: Sym,
    errors: long,

    // ─── ownership ───────────────────────────────────────────────────────────
    // Rebuilt per function; the ownership section at the end of this file says what each holds.
    dropOf:    HashMap<str, long>, // a tracked owning local -> the type whose `drop` releases it
    dropDepth: HashMap<str, long>, // and the loop depth its declaration sits at
    fresh:     HashMap<str, bool>, // declared and not yet stored to: a store releases nothing
    ownParams: HashMap<str, bool>, // this function's parameters, which arrive already owning
    scope:     Vec<OwnLocal>,      // the scope stack, flattened
    scopeBase: Vec<long>,          // where each open scope begins in it
    moved:     Vec<Sym>,           // statically moved on the path walked so far
    // Partial moves (`x.f`, an entry in `moved` named by `partialEntry`): which ones were moved
    // on EVERY path walked so far (`moved` is any path), their owner and field, which got a
    // runtime flag, and the flag writes waiting to learn whether they are needed.
    pmust:     Vec<Sym>,
    pmustLoop: Vec<Sym>,           // `pmust` as each enclosing loop was entered, flattened
    pmustLoopBase: Vec<long>,
    pOwner:    HashMap<str, Sym>,
    pField:    HashMap<str, Sym>,
    pFlags:    Vec<Sym>,           // in the order a release first read each
    pHoles:    Vec<PHole>,
    pCond:     long,               // inside a short-circuit's right operand: a move there is not certain
    loopBase:  Vec<long>,          // `scope.len()` as each enclosing loop was entered
    loopMoved: Vec<Sym>,           // `moved` as each was entered, flattened
    loopMovedBase: Vec<long>,
    loopDepth: long,
    // Inside the body of a `recover`, how many deep. A `raise` can leave the body between any two
    // calls, so there a move is recorded before the statement that makes it, and a scope's
    // release clears the flag of what it released. The tracked locals each open body declares
    // and the values it moves are kept for its handler, flattened, with where each body's run
    // begins.
    ownRecover: long,
    recLocals: Vec<OwnLocal>,
    recLocalsBase: Vec<long>,
    recMoved:  Vec<Sym>,
    recMovedBase: Vec<long>,
    ownSeq:    long,               // unique names for the pass's own temporaries
    ownFn:     long,               // the function node being walked, for its parameter list
    ownSeeding: bool,              // the next block opened is a function body: seed its parameters
    ownDone:   bool,               // the whole-program passes have run
    notedTo:   long,               // how much of the page `runFrom` has noted (fnAt, returns, ...)
    macroOk:   HashMap<str, bool>, // the macros found runnable (`macroRunnable`), by name
    // An arm's bindings move out of the subject one at a time, and the second of them still has
    // to read what the first one moved: the subject the current arm's prologue has taken from.
    bindSubject: Sym,
    bmLocals:  HashMap<str, bool>, // a match through a borrow: the function's locals -> is a borrow
    bmOwnRead: HashMap<str, bool>, // and its by-value parameters passed as borrows (inferred `read`)
    bmCopies:  HashMap<str, long>, // and its bindings noted in `gCopyBinds`, by name
    bmDry:     long,               // `bmArmBlock` noting for that copy what it would refuse, or -1
    bmDestr:   bool,               // and that copy is a destructured name, for the words
    convIdx:   HashMap<str, long>, // parameter name -> its position, while inference scans a body
    capMut:    HashMap<str, bool>, // `<closure>.<capture>` -> the body writes it
    tmpDecl:   HashMap<str, long>, // a hoisted temporary -> its declaration, for its type
    xPath:     Vec<Sym>,           // one call's access paths, components flattened
    tracked:   HashMap<str, bool>, // locals declared with no value yet
    assigned:  Vec<Sym>,           // the subset definitely assigned at this point
    initScope: Vec<Sym>,           // per-scope Drop locals, flattened...
    initBase:  Vec<long>,          // ...and where each open scope begins in it
    eqExtra:   Vec<long>,          // derived `eq` methods, waiting to be added to the page
    fnDone:    HashMap<str, bool>, // bodies already walked, so none is rewritten twice
    // Macros run inside this pass: `ev` runs them, and `page` is what it indexes. A function whose
    // body invokes a macro that cannot run yet (its body or something it calls is unchecked, or a
    // generic it needs is not stamped) is deferred to the next round. `deferReason` says why the
    // last one was, for the driver to report if no round makes progress.
    ev: Evaluator,
    page: long,
    curStmt: long,                 // the page statement being checked, for deferring it
    deferredFns: Vec<long>,
    deferReason: String,
    initSeen: HashMap<str, bool>,  // globals whose initializer a readiness walk already followed
    enforcing: bool,               // the convention walk is judging call sites, not gathering
    enforceFn: long,               // whose body it is walking, for a forwarded borrow's own conv
    curFn:     long,               // the function being typed, for its parameters' conventions
    unsafeDepth: long,             // inside `unsafe`, where `&x` fills rather than lends
    declared:  Vec<Sym>,           // what the function being checked put into `vars`...
    shadowed:  Vec<long>,          // ...and the entry each of those displaced, to put back
    // A declaration whose next statement stores into it needs no `Default` value: the store is
    // what makes it own one. Set by `checkBlock`, the only walk that sees both statements.
    noDefault: bool,
    // The type the expression being checked is stored into, when that is a struct and the
    // expression is a call: a generic callee whose arguments leave a type parameter unbound
    // reads it out of here (`v: Vec<long> = vec![]`). Set by `checkAimed`, taken by `checkCall`.
    expectType: Sym,

    // ─── upstream bodies the evaluator needs ─────────────────────────────────
    // In a package build, a dependency's function is not checked (its facts say what checking it
    // decided) unless code run at compile time reaches it: a macro, or anything a global's
    // initializer calls. `ctSeen` is every name that walk has reached; an external one among
    // them is checked on demand (`demandQ`, by function index), and every checked one is walked
    // in turn (`ctWork`), so the closure is complete before the evaluator runs.
    ctSeen:    HashMap<str, bool>,
    demandQ:   Vec<long>,
    ctWork:    Vec<long>,
    stmtOfFn:  HashMap<str, long>, // a function's name -> the page statement holding it
    // The same walk for code that runs: what checked code reaches, so a lazy method (of an
    // instance a dependency stamped) is checked and compiled only when something calls it.
    rtSeen:    HashMap<str, bool>,
    walkRuntime: bool,

    // ─── derives: `trait T derive m` ─────────────────────────────────────────
    // An implementation the program needed and nobody wrote is stubbed the moment it is needed
    // (its signatures, from the trait, so the call that asked is typed against them) and written
    // by the trait's macro at the end of the round, once that macro can run. `lateFns` are
    // methods of a generic type's conditional impl, stamped after the fact once a derive met its
    // bounds, and checked once the instances they name are laid out; `late` stamps them.
    deriveQ:   Vec<DeriveJob>,
    lateFns:   Vec<long>,
    lateNow:   Vec<long>,
    late:      Mono,
    derivesRun: long,
    // A local declared with its type left to its first store (`isInferType`): name -> its
    // declaration, until that store settles it (`settleInfer`).
    inferAt:   HashMap<str, long>,
    // `&n` of a scalar as a call's argument, waiting for the callee to say it is an `inout` scalar.
    lendingArg: NodeId,
    scalarLends: Vec<NodeId>,
    // A local or parameter array's length, by name: what `xs = [a, b, ...]` is held to.
    arrayLens: HashMap<str, long>
}

local symIn xs:Vec<Sym> x:Sym -> bool {
    for k in 0..xs.len() { if (xs.get(k) == x) { return true; } }
    return false;
}
// A sum type's payload slot (`$Some$0`) or its tag: a field only `match` reaches, and whose moves
// are recorded on the value matched. A tuple's element (`$0`) is an ordinary field.
local isPayloadField n:Sym -> bool {
    return strStartsWith(nameOf(n), "$") && !isTupleField(n);
}
// A field as the author writes it: a tuple's element by its position.
local fieldSpelling n:Sym -> str {
    if (isTupleField(n)) { s: str = nameOf(n); return strSlice(s, 1, s.len - 1); }
    return nameOf(n);
}

// A sum type whose all-zero value is a variant carrying nothing (tag 0, no payload): what an
// omitted `Option<File>` field is, `None`, which owns nothing.
local zeroIsEmptyVariant n:Sym -> bool {
    at: long = gReg.findEnumSym(n);
    if (at < 0) { return false; }
    ed: EnumDef = gReg.enumDef(at);
    if (!ed.hasPayload) { return false; }
    for k in 0..ed.variantCount {
        vd: VariantDef = gReg.variantAt(ed, k);
        if (vd.value == 0) { return vd.payloadCount == 0; }
    }
    return false;
}

// What a struct literal's initializer is said to be stored into, built without allocating (it is
// asked for every field of every literal, and read only when the value does not fit).
local litFieldWhat n:Sym -> str {
    if (isPayloadField(n)) { return "the variant's payload"; }
    return fieldSpelling(n);
}

// How a note names the place a value was stored into: a bare name in backticks, a phrase ("the
// assigned place", "`c`") as it is. A struct literal's field arrives bare, since `litFieldWhat`
// builds nothing unless the store fails; this runs only once it has.
local notePlace what:str -> str {
    for k in 0..what.len {
        c: long = charAt(what, k);
        if (c == ' ' || c == '`') { return what; }
    }
    s: String;
    s.push('`');
    s.pushStr(what);
    s.push('`');
    return keepString(s);
}

// A condition that always holds: a bare `else` is the last link of its chain with one.
local isAlways inout a:Ast cond:NodeId -> bool {
    if (cond == NO_NODE) { return false; }
    e: Expr = a.expr(cond);
    if (e.op != Op.Literal) { return false; }
    match e.payload { Num(v) { return v != 0; } _ { } }
    return false;
}
local nodeIn xs:Vec<NodeId> x:NodeId -> bool {
    for k in 0..xs.len() { if (xs.get(k) == x) { return true; } }
    return false;
}

// Where binding `nm`'s declaration sits in an arm's prologue, with its store the statement after
// it, or -1.
local bindingAt inout a:Ast body:long nm:Sym -> long {
    lim: long = a.blockLen(body) - 1;
    for s in 0..lim {
        st: Stmt = a.stmtAt(body, s);
        if (st.kind == StmtKind.VarDecl && a.decls.get(st.at).name == nm) {
            if (a.stmtAt(body, s + 1).kind != StmtKind.Expr) { return -1; }
            return s;
        }
    }
    return -1;
}

// An argument a call is handed by its address rather than its value, when the parameter does not
// take it: a struct (or a tuple, or an enum with a payload), a borrow, a trait object, a slice, a
// value boxed as `any`. A `str` is a view of bytes safe code never writes or releases.
local byAddressKind k:Lit -> bool {
    return k == Lit.Struct || k == Lit.Tuple || k == Lit.Ref || k == Lit.TraitObj || k == Lit.Slice || k == Lit.Any;
}

// A variant as the source names it: a deferred match's arm reads `?Some` until its type is known.
local variantSpelling v:Sym -> str {
    s: str = nameOf(v);
    if (s.len > 0 && charAt(s, 0) == '?') { return strSlice(s, 1, s.len - 1); }
    return s;
}

methods Checker for Default {
    new -> Checker {
        evl: Evaluator; drs: String; lm: Mono;
        return Checker { vars: map![], types: vec![], fnReturns: map![], fnNames: map![], varNames: map![], locals: map![],
                         fnAt: map![], privateIn: map![], fnBare: BareIndex.new(), diverging: map![], wanted: vec![], wantedClones: vec![], addrOperand: NO_NODE, ownUnsafe: 0, addrFills: vec![], stmtMoves: 0, globalFnRefs: vec![], globalFnRefPos: vec![], guards: 0, withHolds: map![], currentModule: NO_SYM, currentReturn: varType(Lit.Void, NO_SYM),
                         errors: 0,
                         dropOf: map![], dropDepth: map![], fresh: map![], ownParams: map![],
                         scope: vec![], scopeBase: vec![], moved: vec![],
                         pmust: vec![], pmustLoop: vec![], pmustLoopBase: vec![], pOwner: map![],
                         pField: map![], pFlags: vec![], pHoles: vec![], pCond: 0,
                         loopBase: vec![], loopMoved: vec![], loopMovedBase: vec![],
                         loopDepth: 0, ownRecover: 0, recLocals: vec![], recLocalsBase: vec![], recMoved: vec![], recMovedBase: vec![],
                         ownSeq: 0, ownFn: 0, ownSeeding: false, ownDone: false, notedTo: 0, macroOk: map![],
                         bindSubject: NO_SYM, bmLocals: map![], bmOwnRead: map![], bmCopies: map![], bmDry: -1, bmDestr: false,
                         convIdx: map![], capMut: map![], tmpDecl: map![], declared: vec![], shadowed: vec![],
                         xPath: vec![], tracked: map![], assigned: vec![], initScope: vec![], initBase: vec![],
                         eqExtra: vec![], fnDone: map![], ev: evl, page: 0, curStmt: -1, deferredFns: vec![], deferReason: drs, initSeen: map![],
                         enforcing: false, enforceFn: 0, curFn: -1,
                         unsafeDepth: 0, noDefault: false, expectType: NO_SYM,
                         currentFile: NO_SYM, currentPkg: NO_SYM,
                         ctSeen: map![], demandQ: vec![], ctWork: vec![], stmtOfFn: map![],
                         rtSeen: map![], walkRuntime: false,
                         deriveQ: vec![], lateFns: vec![], lateNow: vec![], late: lm, derivesRun: 0,
                         inferAt: map![], lendingArg: NO_NODE, scalarLends: vec![], arrayLens: map![] };
    }
}

methods Checker {
    // ─── the symbol table ────────────────────────────────────────────────────

    note &self name:Sym t:VarType -> void {
        self.types.push(t);
        self.vars.put(nameOf(name), self.types.len() - 1);
    }

    // A file global belongs to the module that declared it, so `counter` in that module means
    // `mod::counter`. Recorded under both spellings, and the bare one is what a use resolves
    // through: the same arrangement functions get.
    noteGlobal &self name:Sym t:VarType -> void {
        self.note(name, t);
        bare: str = lastComponentOf(nameOf(name));
        if (!self.vars.has(bare)) {
            self.types.push(t);
            self.vars.put(bare, self.types.len() - 1);
        }
        self.varNames.put(bare, name);
        self.varNames.put(nameOf(name), name);
    }

    // The qualified name a mention resolves to. A local always wins: it was declared here, and
    // the parser already gave it a name of its own. Then this module's own declaration, if it has
    // one: a file global belongs to the module that declared it, and two modules each owning a
    // `gStdout` is exactly what file-private means. The flat bare-name table cannot express that:
    // whichever module was recorded last took the spelling, so io.k's own writes went to a test
    // file's `long` slot and every `gStdout.inner` in io.k read a field of a type with no fields.
    // Only then the flat table, which is what lets a bare name reach another module's `pub` one.
    resolveVar &self used:Sym -> Sym {
        if (self.locals.has(nameOf(used))) { return used; }
        own: Sym = self.ownDeclared(used, false);
        if (own != used) { return own; }
        hit: Option<Sym> = self.varNames.find(nameOf(used));
        match hit { Some(q) { return q; } None { } }
        return used;
    }

    // `<the module being checked>::<used>`, when that is a name the corresponding table holds;
    // `used` itself otherwise. An already-qualified name never matches, which is what leaves
    // `io::gStdout` meaning io's and not `here::io::gStdout`.
    ownDeclared &self used:Sym wantFn:bool -> Sym {
        if (self.currentModule == NO_SYM) { return used; }
        q: Sym = qualifiedSym(self.currentModule, used);
        if (wantFn) {
            if (self.fnNames.has(nameOf(q))) { return q; }
            return used;
        }
        if (self.varNames.has(nameOf(q))) { return q; }
        return used;
    }
    // A local's entry into the one type table is undoable, because that table also holds the
    // globals and everything a previous function declared. Without the undo, a fn-typed local
    // named `f` in one function is still in scope in the next, where it wins over the real `f`
    // and turns the call into an indirect one through a slot nobody wrote.
    noteLocal &self name:Sym t:VarType -> void {
        prev: long = NOT_FOUND;
        hit: Option<long> = self.vars.find(nameOf(name));
        match hit { Some(i) { prev = i; } None { } }
        self.declared.push(name);
        self.shadowed.push(prev);
        self.note(name, t);
        self.locals.put(nameOf(name), true);
    }

    // The undo, innermost first, so a name declared twice comes back to what it displaced.
    forgetLocals &self -> void {
        k: long = self.declared.len();
        while (k > 0) {
            k = k - 1;
            n: str = nameOf(self.declared.get(k));
            prev: long = self.shadowed.get(k);
            if (prev == NOT_FOUND) { self.vars.remove(n); }
            else { self.vars.put(n, prev); }
        }
        self.declared.clear();
        self.shadowed.clear();
    }
    lookup &self name:Sym -> VarType {
        hit: Option<long> = self.vars.find(nameOf(name));
        match hit { Some(i) { return self.types.get(i); } None { } }
        return varType(Lit.Void, NO_SYM);
    }

    // A function is recorded under its qualified name and also under its bare last component, so
    // a call written `add(...)` finds `mod::add` without the call site having to know which module
    // declared it. The qualified entry is what a `mod::add(...)` call finds.
    noteReturn &self fn:Sym t:VarType -> void {
        self.types.push(t);
        at: long = self.types.len() - 1;
        self.fnReturns.put(nameOf(fn), at);
        bare: str = lastComponentOf(nameOf(fn));
        if (!self.fnReturns.has(bare)) { self.fnReturns.put(bare, at); }
        self.noteFnName(fn);
    }

    // What a name written bare resolves to. A template needs this as much as a function does
    // (`newShared(v)` has to reach `shared::newShared` before its instance can be named), but it
    // has no return type to record, since that is what the instantiation decides.
    noteFnName &self fn:Sym -> void {
        // Once per function: the collection pass walks the page again each driver round, and a
        // chain that grew by one every time would put the cost straight back.
        if (!self.fnNames.has(nameOf(fn))) { self.fnBare.add(fn); }
        self.fnNames.put(lastComponentOf(nameOf(fn)), fn);
        self.fnNames.put(nameOf(fn), fn);
    }

    // The qualified name a call resolves to, or the name as written when nothing declares it.
    resolveFn &self called:Sym -> Sym {
        // This module's own function first, for the same reason a global's own module wins:
        // `sizeClass` is file-private to stdlib/heap.k, and a test file declaring one of its own
        // must not take the spelling away from heap.k's own callers.
        own: Sym = self.ownDeclared(called, true);
        if (own != called) { return own; }
        bare: str = nameOf(called);
        // Then the modules this one includes, the way a type name resolves: two `pub opName`s in
        // two modules are two functions, and which one a call means is decided by what the
        // calling module can see, not by which was registered last under the bare spelling.
        if (self.currentModule != NO_SYM && !gImports.isEmpty() && lastComponentOf(bare).len == bare.len) {
            here: str = nameOf(self.currentModule);
            found: Sym = NO_SYM;
            // Another file's private function is no candidate: nothing here may call it, so it
            // cannot make a name ambiguous (`float.k`'s `local isDigit` beside `chars::isDigit`).
            // It is kept aside only so the refusal can name it when it is the one function of
            // that name in reach.
            hidden: Sym = NO_SYM;
            i: long = self.fnBare.firstOf(bare);
            while (i >= 0) {
                cand: Sym = self.fnBare.qualAt(i);
                own: Sym = self.fnBare.ownerAt(i);
                i = self.fnBare.nextOf(i);
                if (own == NO_SYM || !gImports.reaches(here, own)) { continue; }
                if (!self.privateIn.isEmpty() && self.currentFile != NO_SYM) {
                    pf: Option<Sym> = self.privateIn.find(nameOf(cand));
                    match pf {
                        Some(file) { if (file != self.currentFile) { if (hidden == NO_SYM) { hidden = cand; } continue; } }
                        None { }
                    }
                }
                if (found != NO_SYM && found != cand) {
                    failStr(ambiguousName(bare, BareName { name: found, rival: cand }));
                }
                found = cand;
            }
            if (found != NO_SYM) { return found; }
            if (hidden != NO_SYM) { return hidden; }
        }
        // `ast`'s functions are visible from everywhere, as its types are: a macro body calls
        // `parseExpr` from wherever the macro was declared.
        pre: Sym = qualifiedName("ast", bare);
        if (self.fnNames.has(nameOf(pre))) { return pre; }
        hit: Option<Sym> = self.fnNames.find(bare);
        match hit { Some(q) { return q; } None { } }
        return called;
    }
    // Whether a bare name is a type's, seen from the module being checked. A static call's
    // receiver (`Vec` in `Vec.new()`) is a type name standing where a value is read.
    namesType &self n:Sym -> bool {
        if (gReg.declares(nameOf(n))) { return true; }
        b: BareName = gReg.resolveBareIn(nameOf(self.currentModule), nameOf(n));
        return gReg.declares(nameOf(b.name));
    }
    returnOf &self fn:Sym -> VarType {
        hit: Option<long> = self.fnReturns.find(nameOf(fn));
        match hit { Some(i) { return self.types.get(i); } None { } }
        return varType(Lit.Void, NO_SYM);
    }

    // ─── the walk ────────────────────────────────────────────────────────────

    // Every function's signature first, so a body may call one declared later. Forward references
    // and mutual recursion both work because nothing is typed until every name is known.
    run &self inout a:Ast page:long -> long { return self.runFrom(a, page, 0); }

    // The instantiations found since the last round, handed over and forgotten. A clone made for
    // one of them may ask for more, which is what makes this a loop rather than a single pass.
    takeWanted &self -> Vec<FnRequest> {
        out: Vec<FnRequest>;
        for k in 0..self.wanted.len() { out.push(self.wanted.get(k)); }
        self.wanted.clear();
        return out;
    }

    takeWantedClones &self -> Vec<Sym> {
        out: Vec<Sym>;
        for k in 0..self.wantedClones.len() { out.push(self.wantedClones.get(k)); }
        self.wantedClones.clear();
        return out;
    }

    // Signatures for the whole page, then bodies from `start`. Checking a body rewrites it (a
    // method call becomes an ordinary one) so a body must not be walked twice; a page that grew
    // because a generic function was stamped is re-entered at the first new statement.
    runFrom &self inout a:Ast page:long start:long -> long {
        self.page = page;
        n: long = a.blockLen(page);
        // The page only grows at its end (a round's stamps, the derived methods), so what an
        // earlier round noted is noted: this walks the statements added since. Walking the whole
        // page every round was a twelfth of a package's compile, most of it its dependencies'
        // functions noted again and again.
        k: long = self.notedTo;
        self.notedTo = n;
        while (k < n) {
            st: Stmt = a.stmtAt(page, k);
            if (st.kind == StmtKind.FunctionDef) {
                f: FnNode = a.fns.get(st.at);
                // Two functions of one name. Without this check the second would silently replace
                // the first here, both would be emitted, and the assembler would report a
                // redefined label at a line of generated code. A re-walk of the same function is
                // not a redefinition: the page grows between rounds, so `st.at` is what tells a
                // second definition from the first one's statement written again (a derive's).
                seen: Option<long> = self.fnAt.find(nameOf(f.name));
                match seen {
                    Some(prev) {
                        if (prev != st.at) {
                            a.enterStmt(a.stmtIdAt(page, k));
                            failStr(format("redefinition of `{}`", nameOf(f.name)));
                        }
                    }
                    None { }
                }
                // A template's parameter types are still parameters, so it has no return type to
                // record, but a call has to read those parameters to infer its instance.
                self.fnAt.put(nameOf(f.name), st.at);
                if (f.visibility == Vis.Local && f.file != NO_SYM) { self.privateIn.put(nameOf(f.name), f.file); }
                if (gFloatBoxFormat == NO_SYM && !f.isTemplate && nameOf(f.name) == FLOAT_BOX_FORMAT) {
                    gFloatBoxFormat = f.name;
                    gAddressedFns.push(f.name);      // a float box's `y` is its address
                    gAddressedSigs.push(NO_SYM);
                }
                self.stmtOfFn.put(nameOf(f.name), a.stmtIdAt(page, k));
                if (f.isTemplate) { self.noteFnName(f.name); k = k + 1; continue; }
                self.noteReturn(f.name, varType(f.returnKind, f.returnStruct));
            } else if (st.kind == StmtKind.VarDecl) {
                d: VarDeclNode = a.decls.get(st.at);
                self.noteGlobal(d.name, VarType { kind: d.kind, structName: d.structName, isArray: d.isArray });
            }
            k = k + 1;
        }
        // A closure's body is closed over its capture struct: it names its own parameters, `__cl`
        // and nothing else of the scope it was written in. So it can be typed on its own, and it
        // has to be typed first, because the parser could only guess what an expression body
        // returns (a field read or a call is `void` until this pass runs), and a caller that reads
        // that guess reads the wrong width. Page order already puts an inner closure ahead of the
        // one that holds it, so a single pass in order is enough.
        for k in start..n {
            st: Stmt = a.stmtAt(page, k);
            if (st.kind == StmtKind.FunctionDef && isClosureCall(a.fns.get(st.at).name)) {
                self.curStmt = a.stmtIdAt(page, k);
                self.checkGuarded(a, self.curStmt);
            }
        }
        // The functions an earlier round held back for a macro: the macros they use may have
        // become runnable since. Retried before the new statements, so a macro declared later
        // in the page than its first use is only one round behind it.
        held: Vec<long> = self.takeDeferred();
        for k in 0..held.len() {
            self.curStmt = held.get(k);
            one: Instant = monotonic();
            self.checkGuarded(a, held.get(k));
            if (gTimePhases) {
                ms: long = elapsedUs(one) / 1000;
                if (ms > 10) {
                    st2: Stmt = a.stmts.get(held.get(k));
                    nm: str = "<stmt>";
                    if (st2.kind == StmtKind.FunctionDef) { nm = nameOf(a.fns.get(st2.at).name); }
                    if (st2.kind == StmtKind.VarDecl)     { nm = nameOf(a.decls.get(st2.at).name); }
                    eprintln("    deferred {}: {} ms", nm, ms);
                }
            }
        }
        // Implementations of a generic type that were stamped last round, once a derive met their
        // bounds. Their bodies named instances that had to be laid out first, which they now are.
        lateIds: Vec<long> = self.takeLate();
        for k in 0..lateIds.len() {
            self.curStmt = lateIds.get(k);
            self.checkStmtAt(a, lateIds.get(k));
        }
        for k in start..n {
            self.curStmt = a.stmtIdAt(page, k);
            self.checkGuarded(a, self.curStmt);
        }
        // An error above was reported and the round went on to find the rest: nothing past this
        // point may meet a body an error cut short. The driver stops here (`stopIfErrors`).
        if (gErrorCount > 0) { return self.errors; }
        // The upstream bodies compile-time code reached, checked now; checking one can reach
        // more, so this drains rather than takes a snapshot.
        self.drainDemand(a);
        // The implementations this round needed and nobody wrote: each derive macro that can run
        // now writes its type's, which is checked at once and may need more.
        if (gReg.hasDerives()) { self.runDerives(a); }
        // Whatever this round derived, added to the page before anything reads it whole: the
        // ownership pass and the lowerer meet a derived method like any other definition. The
        // page is rewritten in place, so the id every caller holds still names it.
        if (self.eqExtra.len() > 0) { self.addDerived(a, page); }
        // The whole-program passes, once the program is whole: nothing left to stamp is exactly
        // the condition the driver's stamping loop exits on. Running them a round early would
        // judge a caller against a generic instance that did not exist yet.
        if (!self.ownDone && self.wanted.len() == 0 && self.wantedClones.len() == 0 && self.deferredFns.len() == 0
            && !gReg.hasReleased() && self.deriveWork() == 0) {
            self.ownDone = true;
            // Timed here rather than by the driver: it runs in whichever round the program first
            // becomes whole, so from outside it reads as one round being mysteriously expensive.
            own: Instant = monotonic();
            gPhase = "checking ownership and moves";
            self.ownRun(a, page);
            if (gTimePhases) { eprintln("  ownership + moves + drops: {} ms", elapsedUs(own) / 1000); }
        }
        return self.errors;
    }
    // One page statement, typed in the body of a `recover`: an error in it is reported
    // and the round goes on with the next statement, so one run reports the first error of every
    // function rather than of the first. What typing one function leaves in the checker's own
    // state is put back as the function's own exit would. A closure's body is not given one: the
    // type it returns is settled from its body, and callers typed against an unsettled one would
    // be refused for errors that are not theirs.
    checkGuarded &self inout a:Ast id:long -> void {
        st: Stmt = a.stmts.get(id);
        if (!canRecover() || (st.kind == StmtKind.FunctionDef && a.fns.get(st.at).inferReturn)) {
            self.checkStmtAt(a, id);
            return;
        }
        was: VarType = self.currentReturn;
        wasMod: Sym = self.currentModule;
        wasFile: Sym = self.currentFile;
        wasPkg: Sym = self.currentPkg;
        wasUnsafe: long = self.unsafeDepth;
        wasFn: long = self.curFn;
        wasCtx: Sym = gCtxFn;
        wasInst: Sym = gCtxInst;
        unsafe {
            recover {
                self.checkStmtAt(a, id);
            } else {
                self.forgetLocals();
                self.currentReturn = was;
                self.currentModule = wasMod;
                self.currentFile = wasFile;
                self.currentPkg = wasPkg;
                self.unsafeDepth = wasUnsafe;
                self.curFn = wasFn;
                self.expectType = NO_SYM;
                self.noDefault = false;
                self.bindSubject = NO_SYM;
                gCtxFn = wasCtx;
                gCtxInst = wasInst;
            }
        }
    }

    takeDeferred &self -> Vec<long> {
        out: Vec<long>;
        for k in 0..self.deferredFns.len() { out.push(self.deferredFns.get(k)); }
        self.deferredFns.clear();
        return out;
    }
    deferredCount &self -> long { return self.deferredFns.len(); }

    // What the parser wrote down for a closure's return type was a guess off the syntax of its
    // body, which answers `void` for anything a declaration decides: a field read, a call, an
    // index. Now that the body is typed, the real answer replaces it, on the node, where every
    // caller reads it.
    settleReturn &self inout a:Ast at:long -> void {
        f: FnNode = a.fns.get(at);
        r: VarType = self.blockReturnType(a, f.body);
        if (r.kind == Lit.Void) { return; }
        if (r.kind == f.returnKind && r.structName == f.returnStruct) { return; }
        a.fns.set(at, FnNode { name: f.name, returnKind: r.kind, returnStruct: r.structName,
                               visibility: f.visibility, file: f.file, pkg: f.pkg,
                               isUnsafe: f.isUnsafe, isTemplate: f.isTemplate,
                               firstBound: f.firstBound, boundCount: f.boundCount,
                               firstArg: f.firstArg, argCount: f.argCount, body: f.body,
                               inferReturn: false, attrs: f.attrs });
        self.noteReturn(f.name, r);
    }

    // The type the first `return` reached in a body yields. The same search the parser makes over
    // the syntax, asked again of the typed tree.
    blockReturnType &self inout a:Ast b:long -> VarType {
        none: VarType = varType(Lit.Void, NO_SYM);
        for k in 0..a.blockLen(b) {
            st: Stmt = a.stmtAt(b, k);
            if (st.kind == StmtKind.Return) {
                v: NodeId = a.returns.get(st.at).value;
                if (v == NO_NODE) { return none; }
                e: Expr = a.expr(v);
                return varType(e.kind, e.structName);
            }
            inner: VarType = self.nestedReturnType(a, st);
            if (inner.kind != Lit.Void) { return inner; }
        }
        return none;
    }

    nestedReturnType &self inout a:Ast st:Stmt -> VarType {
        none: VarType = varType(Lit.Void, NO_SYM);
        if (st.kind == StmtKind.If) {
            at: long = st.at;
            while (at >= 0) {
                nd: IfNode = a.ifs.get(at);
                r: VarType = self.blockReturnType(a, nd.body);
                if (r.kind != Lit.Void) { return r; }
                at = nd.elseIf;
            }
            return none;
        }
        if (st.kind == StmtKind.While) { return self.blockReturnType(a, a.whiles.get(st.at).body); }
        if (st.kind == StmtKind.Recover) {
            r: VarType = self.blockReturnType(a, a.whiles.get(st.at).body);
            if (r.kind != Lit.Void) { return r; }
            return self.blockReturnType(a, a.whiles.get(st.at).step);
        }
        if (st.kind == StmtKind.Loop || st.kind == StmtKind.Unsafe || st.kind == StmtKind.Block) {
            return self.blockReturnType(a, a.blockStmts.get(st.at).body);
        }
        if (st.kind == StmtKind.With) { return self.blockReturnType(a, a.withs.get(st.at).body); }
        if (st.kind == StmtKind.Match) {
            m: MatchNode = a.matches.get(st.at);
            for k in 0..m.armCount {
                r: VarType = self.blockReturnType(a, a.arms.get(m.firstArm + k).body);
                if (r.kind != Lit.Void) { return r; }
            }
        }
        return none;
    }

    addDerived &self inout a:Ast page:long -> void {
        b: Block = a.blocks.get(page);
        ids: Vec<long>;
        for k in 0..b.stmtCount { ids.push(a.stmtRuns.get(b.firstStmt + k)); }
        ids.extend(self.eqExtra);
        self.eqExtra.clear();
        first: long = a.stmtRuns.len();
        a.stmtRuns.extend(ids);
        a.blocks.set(page, Block { firstStmt: first, stmtCount: ids.len() });
    }

    // A declaration is told whether the statement after it stores into it, so a `Default` type
    // is not built only to be overwritten, and so the store has nothing to release.
    checkBlock &self inout a:Ast b:long -> void {
        // The length is re-read each round rather than taken once: a destructure is written out
        // here into several statements, so the block it sits in grows under the walk.
        was: long = gPos;
        k: long = 0;
        while (k < a.blockLen(b)) {
            a.enterStmt(a.stmtIdAt(b, k));
            st: Stmt = a.stmtAt(b, k);
            if (st.kind == StmtKind.Destructure) {
                k = k + self.desugarDestructure(a, b, k);
                continue;
            }
            if (st.kind == StmtKind.Expr && self.arrayAssign(a, a.exprStmts.get(st.at).value)) {
                self.desugarArrayAssign(a, b, k);
                st = a.stmtAt(b, k);
            }
            // `m!(...)` as a statement: what the macro returns replaces the statement, either as a
            // Block of the statements it produced or as an expression statement.
            if (st.kind == StmtKind.Expr && a.expr(a.exprStmts.get(st.at).value).op == Op.MacroCall) {
                self.expandMacroStmt(a, a.stmtIdAt(b, k));
                st = a.stmtAt(b, k);
            }
            self.noDefault = false;
            if (st.kind == StmtKind.VarDecl && k + 1 < a.blockLen(b)) {
                self.noDefault = self.storesInto(a, a.stmtAt(b, k + 1), a.decls.get(st.at).name);
            }
            self.checkStmt(a, st);
            k = k + 1;
        }
        gPos = was;
    }

    // A page statement, checked where it stands: what an error in it is reported at.
    checkStmtAt &self inout a:Ast id:long -> void {
        was: long = a.enterStmt(id);
        self.checkStmt(a, a.stmts.get(id));
        gPos = was;
    }

    // Report from where function `at` is defined: for what is said of a function as a whole.
    atFn &self inout a:Ast at:long -> void {
        if (at < 0) { return; }
        hit: Option<long> = self.stmtOfFn.find(nameOf(a.fns.get(at).name));
        match hit { Some(s) { a.enterStmt(s); } None { } }
    }

    // Replace statement `k` of block `b` with `ids`. The run is rebuilt at the end of `stmtRuns`,
    // which is what keeps a block's statements contiguous while its neighbours keep theirs.
    spliceStmts &self inout a:Ast b:long k:long ids:Vec<long> -> void {
        run: Vec<long>;
        n: long = a.blockLen(b);
        for j in 0..n {
            if (j == k) { run.extend(ids); } else { run.push(a.stmtIdAt(b, j)); }
        }
        first: long = a.stmtRuns.len();
        a.stmtRuns.extend(run);
        a.blocks.set(b, Block { firstStmt: first, stmtCount: run.len() });
    }

    // `place = [a, b, ...]` (not a declaration's initializer, which the parser wrote out).
    arrayAssign &self inout a:Ast id:NodeId -> bool {
        e: Expr = a.expr(id);
        return e.op == Op.Assignment && e.right != NO_NODE && a.expr(e.right).op == Op.ArrayLit;
    }

    // `place = [v0, v1, ...]` into an array place (a local, a parameter, a global, a field of one,
    // through any number of fields): every element given, as a declaration's literal must, each
    // value computed into a hidden local first and only then stored, so a value may read the
    // array it replaces (`xs = [xs[1], xs[0]]`). A constant needs no hidden local. In a block of
    // its own, which is what releases nothing twice: each hidden local is moved into its element.
    //
    //     { $alN_0: T = v0; ...; place[0] = $alN_0; place[1] = 7; ... }
    desugarArrayAssign &self inout a:Ast b:long k:long -> void {
        id: long = a.stmtIdAt(b, k);
        e: Expr = a.expr(a.exprStmts.get(a.stmts.get(id).at).value);
        place: NodeId = e.left;
        n: long = self.placeArrayLen(a, place);
        et: VarType = self.placeIsArray(a, place);
        if (n < 0 || !et.isArray) {
            failStr(stringOf("cannot assign an array literal to this place\nnote: an array literal `[a, b, ...]` is assigned whole only to an array: a local, a parameter, a global or a field of one (`xs = [...]`, `s.cells = [...]`)"));
        }
        lit: Expr = a.expr(e.right);
        ln: LitNode = a.lits.get(0);
        match lit.payload { Lit(l) { ln = a.lits.get(l); } _ { } }
        if (ln.initCount != n) {
            failStr(format("wrong number of elements in an array literal: expected {}, found {}\nnote: an array literal names every element of the array",
                           n, ln.initCount));
        }
        ids: Vec<long>;
        vals: Vec<NodeId>;
        tag: long = self.guards;
        self.guards = self.guards + 1;
        for j in 0..n {
            v: NodeId = a.inits.get(ln.firstInit + j).value;
            if (a.expr(v).op == Op.Literal || n == 1) { vals.push(v); continue; }
            hold: Sym = internString(format("$al{}_{}", tag, j));
            a.decls.push(VarDeclNode { name: hold, kind: et.kind, structName: et.structName,
                                       isArray: false, count: 0, conv: Conv.None, isVariadic: false,
                                       elemKind: Lit.Void, elemStruct: NO_SYM, init: NO_NODE });
            ids.push(a.addStmt(StmtKind.VarDecl, a.decls.len() - 1));
            lhs: NodeId = a.leafOf(Op.Lvalue, Payload.Name(hold), et.kind, et.structName);
            a.exprStmts.push(ExprStmtNode { value: a.binary(Op.Assignment, lhs, v, et.kind) });
            ids.push(a.addStmt(StmtKind.Expr, a.exprStmts.len() - 1));
            vals.push(a.leafOf(Op.Lvalue, Payload.Name(hold), et.kind, et.structName));
        }
        for j in 0..n {
            base: NodeId = place;
            if (j > 0) { base = clonePlace(a, place); }
            a.indexes.push(IndexNode { name: NO_SYM, base: base, index: a.leaf(Op.Literal, Payload.Num(j), Lit.Long), whole: false,
                                       rawPointerBase: false, sliceStart: NO_NODE, sliceEnd: NO_NODE, at: NO_SYM });
            el: NodeId = a.leafOf(Op.ArrayIndex, Payload.Index(a.indexes.len() - 1), et.kind, et.structName);
            a.exprStmts.push(ExprStmtNode { value: a.binary(Op.Assignment, el, vals.get(j), et.kind) });
            ids.push(a.addStmt(StmtKind.Expr, a.exprStmts.len() - 1));
        }
        a.blockStmts.push(BlockStmtNode { body: a.addBlock(ids) });
        blk: long = a.addStmt(StmtKind.Block, a.blockStmts.len() - 1);
        one: Vec<long>;
        one.push(blk);
        self.spliceStmts(a, b, k, one);
    }

    // The length of the array a place made of names and fields names, or -1.
    placeArrayLen &self inout a:Ast id:NodeId -> long {
        e: Expr = a.expr(id);
        match e.payload {
            Name(n) {
                q: Sym = self.resolveVar(n);
                hit: Option<long> = self.arrayLens.find(nameOf(q));
                match hit { Some(c) { if (self.locals.has(nameOf(q))) { return c; } } None { } }
                gi: long = gReg.findGlobalSym(q);
                if (gi >= 0 && gReg.globalDef(gi).isArray) { return gReg.globalDef(gi).count; }
            }
            Field(f) {
                fd: FieldNode = a.fields.get(f);
                bt: VarType = self.placeIsArray(a, fd.base);
                if (bt.isArray || (bt.kind != Lit.Struct && bt.kind != Lit.Ref)) { return -1; }
                si: long = gReg.findStructSym(bt.structName);
                if (si < 0) { return -1; }
                d: StructDef = gReg.structDef(si);
                fi: long = gReg.findFieldSym(d, fd.name);
                if (fi < 0) { return -1; }
                fdef: FieldDef = gReg.fieldAt(d, fi);
                if (fdef.isArray) { return fdef.count; }
            }
            _ { }
        }
        return -1;
    }

    // `q, r = f();`: the names take the tuple's fields by position. A tuple is registered as an
    // ordinary struct, so this is one hidden local holding the returned value and one declaration
    // per name reading a field out of it:
    //
    //     $tupN: (A, B) = f();   q: A = $tupN.$0;   r: B = $tupN.$1;
    //
    // Written out here so nothing downstream has to know destructuring exists: the same move
    // `with` makes. The names must stay in the enclosing scope, so the statements are spliced into
    // the block rather than wrapped in one of their own.
    //
    // Answers how many of the statements it wrote are already checked, which is the one holding
    // the call: re-checking a call would resolve its name and box its arguments a second time.
    desugarDestructure &self inout a:Ast b:long k:long -> long {
        id: long = a.stmtIdAt(b, k);
        ds: DestructureNode = a.destructures.get(a.stmts.get(id).at);
        t: VarType = self.checkExpr(a, ds.value);
        // A tuple, as a value or as a borrow of one (`v.at(i)`, `v[i]`): not a pointer to one, nor
        // a slice of them, whose type names a tuple too.
        isRef: bool = t.kind == Lit.Ref;
        si: long = -1;
        if ((t.kind == Lit.Tuple || t.kind == Lit.Struct || isRef) && !t.isArray && isTupleName(t.structName)) {
            si = gReg.findStructSym(t.structName);
        }
        if (si < 0) {
            failStr(format("cannot destructure a value of type `{}`\nnote: only a tuple can be taken apart into names",
                           typeMangleName(t.kind, t.structName)));
        }
        d: StructDef = gReg.structDef(si);
        if (d.fieldCount != ds.nameCount) {
            failStr(format("cannot destructure a {}-element tuple into {}",
                           d.fieldCount, plural(ds.nameCount, "name")));
        }
        // A tuple's own kind is `Lit.Tuple`, which only the type table knows the shape of; as the
        // struct it is registered as, every path that sizes, copies or reads a field of an
        // aggregate already handles it. A borrow keeps its type: the hidden local reads what it
        // points at, and a destructure through a borrow makes its names borrows of it
        // (`bmDestructure`). Stamped as the tuple, the call returning it would have been called as
        // one returning a tuple, with a result slot it never fills ahead of its arguments.
        if (!isRef) { self.stamp(a, ds.value, varType(Lit.Struct, t.structName)); }

        // Each written as a declaration and a store, the shape the parser gives `x: T = v;`, so
        // the ownership walk sees each name take its field out of the hidden local (a partial
        // move, so each is released once and the hidden local releases what is left, which is
        // nothing), and a match through a borrow can make every one of them a borrow instead.
        hold: Sym = internString(format("$tup{}", self.guards));
        self.guards = self.guards + 1;
        ids: Vec<long>;
        a.decls.push(VarDeclNode { name: hold, kind: Lit.Struct, structName: t.structName,
                                   isArray: false, count: 0, conv: Conv.None, isVariadic: false,
                                   elemKind: Lit.Void, elemStruct: NO_SYM, init: NO_NODE });
        ids.push(a.addStmt(StmtKind.VarDecl, a.decls.len() - 1));
        self.noteLocal(hold, varType(Lit.Struct, t.structName));
        held: NodeId = a.leafOf(Op.Lvalue, Payload.Name(hold), Lit.Struct, t.structName);
        a.exprStmts.push(ExprStmtNode { value: a.addExpr(Expr { op: Op.Assignment, left: held, right: ds.value,
                                                              kind: Lit.Struct, structName: t.structName,
                                                              isParen: false, payload: Payload.None }) });
        ids.push(a.addStmt(StmtKind.Expr, a.exprStmts.len() - 1));

        discards: Vec<long>;
        for j in 0..ds.nameCount {
            f: FieldDef = gReg.fieldAt(d, j);
            nm: Sym = a.names.get(ds.firstName + j);
            // `_`: nothing declared. An element that owns something is taken out into a hidden
            // local in a block of its own, after the names, so it is released at once.
            if (nameOf(nm) == "_") {
                if (f.kind == Lit.Struct && gReg.needsDrop(f.structName)) { discards.push(j); }
                continue;
            }
            base: NodeId = a.leafOf(Op.Lvalue, Payload.Name(hold), Lit.Struct, t.structName);
            a.fields.push(FieldNode { base: base, name: f.name });
            v: NodeId = a.leafOf(Op.FieldAccess, Payload.Field(a.fields.len() - 1),
                                 f.kind, f.structName);
            a.decls.push(VarDeclNode { name: nm, kind: f.kind,
                                       structName: f.structName, isArray: false, count: 0,
                                       conv: Conv.None, isVariadic: false, elemKind: Lit.Void,
                                       elemStruct: NO_SYM, init: NO_NODE });
            ids.push(a.addStmt(StmtKind.VarDecl, a.decls.len() - 1));
            lhs: NodeId = a.leafOf(Op.Lvalue, Payload.Name(nm), f.kind, f.structName);
            a.exprStmts.push(ExprStmtNode { value: a.binary(Op.Assignment, lhs, v, f.kind) });
            ids.push(a.addStmt(StmtKind.Expr, a.exprStmts.len() - 1));
        }
        for j in discards {
            f: FieldDef = gReg.fieldAt(d, j);
            dn: Sym = internString(format("$discT{}", self.guards));
            self.guards = self.guards + 1;
            base: NodeId = a.leafOf(Op.Lvalue, Payload.Name(hold), Lit.Struct, t.structName);
            a.fields.push(FieldNode { base: base, name: f.name });
            v: NodeId = a.leafOf(Op.FieldAccess, Payload.Field(a.fields.len() - 1), f.kind, f.structName);
            inner: Vec<long>;
            a.decls.push(VarDeclNode { name: dn, kind: f.kind, structName: f.structName, isArray: false, count: 0,
                                       conv: Conv.None, isVariadic: false, elemKind: Lit.Void,
                                       elemStruct: NO_SYM, init: NO_NODE });
            inner.push(a.addStmt(StmtKind.VarDecl, a.decls.len() - 1));
            lhs: NodeId = a.leafOf(Op.Lvalue, Payload.Name(dn), f.kind, f.structName);
            a.exprStmts.push(ExprStmtNode { value: a.binary(Op.Assignment, lhs, v, f.kind) });
            inner.push(a.addStmt(StmtKind.Expr, a.exprStmts.len() - 1));
            a.blockStmts.push(BlockStmtNode { body: a.addBlock(inner) });
            ids.push(a.addStmt(StmtKind.Block, a.blockStmts.len() - 1));
        }
        self.spliceStmts(a, b, k, ids);
        return 2;
    }

    // Is `st` a bare `name = ...`? That, and only that, is a store that makes the declaration's
    // own value pointless: a store to a field reads the rest of the value it writes into.
    storesInto &self inout a:Ast st:Stmt name:Sym -> bool {
        // `x = f()?;`: the store is the last statement of the `?`'s `else` (`Parser.wrapTry`:
        // `$tryN` declared and stored, then `if ($tryN.isBreak()) { ... } else { ... }`).
        if (st.kind == StmtKind.Block) {
            b: long = a.blockStmts.get(st.at).body;
            if (a.blockLen(b) != 3 || a.stmtAt(b, 0).kind != StmtKind.VarDecl || a.stmtAt(b, 2).kind != StmtKind.If) { return false; }
            if (!strStartsWith(nameOf(a.decls.get(a.stmtAt(b, 0).at).name), "$try")) { return false; }
            f: IfNode = a.ifs.get(a.stmtAt(b, 2).at);
            if (f.elseIf < 0) { return false; }
            ok: long = a.ifs.get(f.elseIf).body;
            if (a.blockLen(ok) == 0) { return false; }
            return self.storesInto(a, a.stmtAt(ok, a.blockLen(ok) - 1), name);
        }
        if (st.kind != StmtKind.Expr) { return false; }
        e: Expr = a.expr(a.exprStmts.get(st.at).value);
        if (e.op != Op.Assignment || e.left == NO_NODE) { return false; }
        l: Expr = a.expr(e.left);
        if (l.op != Op.Lvalue) { return false; }
        p: Payload = l.payload;
        match p { Name(x) { return nameOf(x) == nameOf(name); } _ { } }
        return false;
    }

    // A declaration: a local in a body, or a global on the page.
    checkVarDecl &self inout a:Ast st:Stmt -> void {
        d: VarDeclNode = a.decls.get(st.at);
        // A dependency's global: its initializer ran (or was folded) where it was compiled.
        if (self.curFn < 0 && isExternGlobal(d.name)) { return; }
        // A global whose initializer calls a macro not yet runnable is held back like a
        // function is, and retried next round: `gOpNames: Vec<str> = vec![...]` in a module
        // checked before `vec`'s own body was.
        if (self.curFn < 0 && d.init != NO_NODE && !self.exprMacrosReady(a, d.init)) {
            self.deferredFns.push(self.curStmt);
            return;
        }
        // A local whose type its first store says: noted as nothing until then.
        if (self.curFn >= 0 && isInferType(d.kind, d.structName)) {
            self.noteLocal(d.name, varType(Lit.Void, NO_SYM));
            self.inferAt.put(nameOf(d.name), st.at);
            return;
        }
        self.noteLocal(d.name, VarType { kind: d.kind, structName: d.structName, isArray: d.isArray });
        if (d.isArray) { self.arrayLens.put(nameOf(d.name), d.count); }
        // A borrow lives across the call that makes it and no longer. Bound to a local it
        // outlives that, and nothing after it is checked: `p: &Res = v[0]` then `v.push(..)`
        // reallocates the vector and leaves `p` pointing at the old block. A borrow is a way
        // of passing a value, not of holding one, which is why parameters may be `&T` and
        // locals may not.
        if (self.curFn >= 0 && self.unsafeDepth == 0 && d.kind == Lit.Ref && !isTempName(d.name)) {
            failStr(format("cannot hold a borrow in the local `{}`\nnote: `{}` has type `{}`, and a borrow lives only across the call that makes it\nhelp: take the value, or use it where it is made",
                           nameOf(d.name), nameOf(d.name), self.spellType(d.kind, d.structName)));
        }
        if (d.init == NO_NODE) {
            self.defaultInit(a, st.at, d);
            built: NodeId = a.decls.get(st.at).init;
            if (self.curFn < 0 && built != NO_NODE && !gUpstreamPkgs.isEmpty()) { self.ctReachExpr(a, built); self.drainWalk(a); self.rtWalkExpr(a, built); }
            return;
        }
        // `X: [T; N] = [a, b, ...]`: each element held to T as a store to one is. (A local's
        // literal was written out as those stores by the parser.)
        if (a.expr(d.init).op == Op.ArrayLit) {
            lit: Expr = a.expr(d.init);
            ln: LitNode = a.lits.get(0);
            match lit.payload { Lit(l) { ln = a.lits.get(l); } _ { } }
            for k in 0..ln.initCount {
                v: NodeId = a.inits.get(ln.firstInit + k).value;
                self.requireAssignable(a, varType(d.kind, d.structName), self.checkAimed(a, v, d.structName), v,
                                       keepString(format("element {} of `{}`", k, nameOf(d.name))));
            }
            if (self.curFn < 0 && !gUpstreamPkgs.isEmpty()) { self.ctReachExpr(a, d.init); self.drainWalk(a); self.rtWalkExpr(a, d.init); }
            return;
        }
        // `keepString`, not the `String` itself: `what` is declared `str`, and handing it a String
        // would read the first 16 bytes of a 24-byte value. That happens to work, because
        // {ptr,len} is a prefix of {ptr,len,cap}, but the argument check rightly refuses it.
        self.requireAssignable(a, VarType { kind: d.kind, structName: d.structName, isArray: d.isArray },
                               self.checkAimed(a, d.init, d.structName), d.init,
                               keepString(format("`{}`", nameOf(d.name))));
        if (d.isArray) { self.requireArrayLen(a, d.count, d.init, keepString(format("`{}`", nameOf(d.name)))); }
        // A global's initializer is run by the evaluator, so whatever upstream code it can
        // reach has to be checked here before that happens.
        if (self.curFn < 0 && !gUpstreamPkgs.isEmpty()) { self.ctReachExpr(a, d.init); self.drainWalk(a); self.rtWalkExpr(a, d.init); }
        return;
    }

    checkStmt &self inout a:Ast st:Stmt -> void {
        if (st.kind == StmtKind.FunctionDef) {
            f: FnNode = a.fns.get(st.at);
            // A template is a pattern whose types are still parameters. Its clones are what gets
            // checked; typing the pattern itself would be typing `T`.
            if (f.isTemplate) { return; }
            // A dependency's body still in its `.klib`: read only for the check that needs it.
            if (f.body == BODY_LAZY) {
                if (!self.ctSeen.has(nameOf(f.name)) || self.fnDone.has(nameOf(f.name))) { return; }
                f = ensureBody(a, st.at);
            }
            // An instance's method left unstamped (a dependency compiled it, or nothing here has
            // reached it yet): stamped once something here needs it. It waits a round when its
            // body names an instance the program had not asked for, which is stamped first.
            if (f.body == BODY_STAMP) {
                key: str = nameOf(f.name);
                if (self.fnDone.has(key)) { return; }
                if (!self.ctSeen.has(key) && !(isLazyFn(st.at) && self.rtSeen.has(key))) { return; }
                if (self.late.stampBody(a, st.at)) {
                    self.deferredFns.push(self.curStmt);
                    self.deferReason.clear();
                    self.deferReason.pushString(format("`{}` waits for the instances its body names to be stamped", key));
                    return;
                }
                f = a.fns.get(st.at);
            }
            // Declared, not defined: its body is in another object. There is nothing here to
            // type, and its signature was recorded by `noteReturn` with every other function's.
            if (f.body < 0) { return; }
            // Checking a body rewrites it, so it must not be walked a second time: a closure's
            // was typed ahead of the page for its return type, and any function may have been
            // checked ahead of its turn, or held back for one.
            if (self.fnDone.has(nameOf(f.name))) { return; }
            // A dependency's body: its own package checked it, and the facts table says what
            // that decided. Checked here only when compile-time code reaches it.
            if (isExternFn(st.at) && !self.ctSeen.has(nameOf(f.name))) { return; }
            // A method of an instance a dependency already stamped: checked when reached.
            if (isLazyFn(st.at) && !self.ctSeen.has(nameOf(f.name)) && !self.rtSeen.has(nameOf(f.name))) { return; }
            if (!self.macrosReady(a, f.body)) { self.deferredFns.push(self.curStmt); return; }
            self.fnDone.put(nameOf(f.name), true);
            // `main`'s result is the exit status (its low 8 bits): any integer type says one.
            if (nameOf(f.name) == "main" && !isInteger(f.returnKind)) {
                failStr(format("`main` has invalid return type `{}`\nnote: its result is the process's exit status (the low 8 bits), so it must be an integer\nhelp: declare it `-> int` or `-> long` (any integer type)",
                               self.spellType(f.returnKind, f.returnStruct)));
            }
            was: VarType = self.currentReturn;
            wasMod: Sym = self.currentModule;
            wasFile: Sym = self.currentFile;
            wasPkg: Sym = self.currentPkg;
            self.currentFile = f.file;
            self.currentPkg = f.pkg;
            wasUnsafe: long = self.unsafeDepth;
            wasFn: long = self.curFn;
            self.curFn = st.at;
            wasCtx: Sym = gCtxFn;
            wasInst: Sym = gCtxInst;
            enterFn(f.name);
            // An `unsafe` function's body is one trusted region from its first statement. So is a
            // closure's `call` written inside `unsafe` code, and no other.
            self.unsafeDepth = 0;
            if (f.isUnsafe) { self.unsafeDepth = 1; }
            self.currentModule = intern(stemOf(nameOf(f.file)));
            self.currentReturn = varType(f.returnKind, f.returnStruct);
            self.locals.clear();
            self.declared.clear();
            self.shadowed.clear();
            for k in 0..f.argCount {
                p: VarDeclNode = a.paramAt(f, k);
                self.noteLocal(p.name, VarType { kind: p.kind, structName: p.structName, isArray: p.isArray });
                if (p.isArray) { self.arrayLens.put(nameOf(p.name), p.count); }
            }
            self.checkBlock(a, f.body);
            // What the parser could only guess at. A closure written without `-> T` returns
            // whatever its body returns, and until this pass has run over that body nobody knows
            // what that is: `|v| v.value * 2` reads `void` from the syntax alone. The answer is
            // written back onto the node, which is where every caller reads it.
            if (f.inferReturn) { self.settleReturn(a, st.at); }
            self.forgetLocals();
            self.currentReturn = was;
            self.currentModule = wasMod;
            self.currentFile = wasFile;
            self.currentPkg = wasPkg;
            self.unsafeDepth = wasUnsafe;
            self.curFn = wasFn;
            gCtxFn = wasCtx;
            gCtxInst = wasInst;
            if (isExternFn(st.at) || isLazyFn(st.at)) { markExternReady(st.at); }
            // What it calls is reached at runtime too, which is what makes a lazy method needed.
            if (!gKnownInstances.isEmpty() && !isExternFn(st.at)) { self.rtWalk(a, f.body); }
            // Reached by compile-time code before it was checked: what it calls is reached too.
            if (self.ctSeen.has(nameOf(f.name))) { self.ctWork.push(st.at); }
            return;
        }
        if (st.kind == StmtKind.VarDecl) {
            // A global's initializer is read in its own module, as a function body is: a method
            // of a trait that module owns is that module's (`Checker.ownTraitMethod`).
            if (self.curFn < 0) {
                wasMod: Sym = self.currentModule;
                wasFile: Sym = self.currentFile;
                wasPkg: Sym = self.currentPkg;
                q: str = nameOf(a.decls.get(st.at).name);
                cut: long = q.len - lastComponentOf(q).len;
                if (cut > 2) { self.currentModule = intern(strSlice(q, 0, cut - 2)); }
                gi: long = gReg.findGlobal(q);
                if (gi >= 0) { self.currentFile = gReg.globalDef(gi).file; self.currentPkg = gReg.globalDef(gi).pkg; }
                self.checkVarDecl(a, st);
                self.currentModule = wasMod;
                self.currentFile = wasFile;
                self.currentPkg = wasPkg;
                return;
            }
            self.checkVarDecl(a, st);
            return;
        }
        if (st.kind == StmtKind.If) { self.checkIf(a, st.at); return; }
        // A `raise` under the body abandons every frame between it and here without releasing
        // what they own, which is what makes a `recover` unsafe.
        if (st.kind == StmtKind.Recover) {
            self.requireUnsafe("`recover`");
            if (self.recoverTarget(a) == NO_SYM) {
                failStr(stringOf("`recover` needs its runtime from `stdlib::recover`
note: no function in the program is marked `@recover`
help: add `#include <stdlib::recover>`"));
            }
            w: WhileNode = a.whiles.get(st.at);
            self.checkBlock(a, w.body);
            self.checkBlock(a, w.step);
            return;
        }
        if (st.kind == StmtKind.While) {
            w: WhileNode = a.whiles.get(st.at);
            self.checkExpr(a, w.cond);
            self.checkBlock(a, w.body);
            if (w.step >= 0) { self.checkBlock(a, w.step); }
            return;
        }
        // The same node carries an `unsafe { }` and a bare block, and only the kind tells them
        // apart: a bare block scopes its statements without granting anything.
        if (st.kind == StmtKind.Unsafe) {
            self.unsafeDepth = self.unsafeDepth + 1;
            self.checkBlock(a, a.blockStmts.get(st.at).body);
            self.unsafeDepth = self.unsafeDepth - 1;
            return;
        }
        if (st.kind == StmtKind.Loop || st.kind == StmtKind.Block) {
            self.checkBlock(a, a.blockStmts.get(st.at).body);
            return;
        }
        if (st.kind == StmtKind.With) { self.desugarWith(a, st.at); return; }
        if (st.kind == StmtKind.Return) {
            r: ReturnNode = a.returns.get(st.at);
            if (r.value != NO_NODE) {
                got: VarType = self.checkAimed(a, r.value, self.currentReturn.structName);
                self.holdFloat(a, r.value, self.currentReturn.kind, got.kind, "the return value");
                self.holdReturn(a, r.value, got);
            } else { self.holdReturn(a, NO_NODE, varType(Lit.Void, NO_SYM)); }
            self.checkReturnedBorrow(a, r.value);
            return;
        }
        if (st.kind == StmtKind.Expr) {
            v: NodeId = a.exprStmts.get(st.at).value;
            self.requireUsed(a, v, self.checkExpr(a, v));
            return;
        }
        if (st.kind == StmtKind.Destructure) {
            self.checkExpr(a, a.destructures.get(st.at).value);
            return;
        }
        if (st.kind == StmtKind.Match) {
            self.resolveMatch(a, st.at);
            m: MatchNode = a.matches.get(st.at);
            for k in 0..m.armCount {
                self.checkExpr(a, a.arms.get(m.firstArm + k).test);
                self.checkBlock(a, a.arms.get(m.firstArm + k).body);
            }
            return;
        }
        if (st.kind == StmtKind.Asm) {
            self.requireUnsafe("an `asm` block");
            n: AsmNode = a.asms.get(st.at);
            for k in 0..n.pieceCount {
                p: AsmPiece = a.asmPieces.get(n.firstPiece + k);
                if (p.value != NO_NODE) { self.checkExpr(a, p.value); }
                // An `out` names what it writes the way a read names what it reads: a local
                // first, then a global of this module or one it sees, held to that global's
                // visibility. The piece takes the global's own name, so the passes after this
                // one, and the lowerer that stores through it, see the global and not a slot
                // that happens to share its spelling.
                if (p.kind == AsmKind.Out) {
                    q: Sym = self.resolveVar(p.name);
                    if (!self.locals.has(nameOf(q))) {
                        if (gReg.findGlobalSym(q) < 0) { failStr(format("cannot find value `{}` in this scope", nameOf(p.name))); }
                        self.requireGlobalVisible(q);
                    }
                    if (q != p.name) { p.name = q; a.asmPieces.set(n.firstPiece + k, p); }
                }
            }
            return;
        }
    }

    checkIf &self inout a:Ast at:long -> void {
        n: IfNode = a.ifs.get(at);
        if (n.cond != NO_NODE) { self.checkExpr(a, n.cond); }
        self.checkBlock(a, n.body);
        if (n.elseIf >= 0) { self.checkIf(a, n.elseIf); }
    }

    // ─── expressions ─────────────────────────────────────────────────────────

    // Type `id` and everything under it, stamping the result on the node. Returns what it decided,
    // so the callers that need it do not have to read the node back.
    checkExpr &self inout a:Ast id:NodeId -> VarType {
        if (id == NO_NODE) { return varType(Lit.Void, NO_SYM); }
        e: Expr = a.expr(id);

        // `v[i] = x` on a type implementing `IndexSet` is `v.setAt(i, x)`. It has to be decided
        // here, ahead of the operands below: typing the left side first would rewrite `v[i]` into
        // its read form `v.at(i)` and leave an assignment whose target is a call.
        if (e.op == Op.Assignment && self.tryIndexSet(a, id)) { return self.checkExpr(a, id); }
        if (e.op == Op.Assignment && self.inferAt.len() > 0) {
            tgt: Sym = self.inferTarget(a, e.left);
            if (tgt != NO_SYM) { return self.settleInfer(a, id, tgt); }
        }
        if (e.op == Op.Assignment) { self.checkSliceStore(a, e.left); self.refuseScalarSelfStore(a, e.left); }

        // `nameof(E, v)` becomes a call to a derived `E_nameof`, so nothing downstream knows the
        // builtin exists: exactly as `sizeof` becomes a literal. Rewritten here rather than
        // walked below: its payload is the operand, which the `Sub` arm would otherwise hand to
        // `checkSub` as a cast or a dereference.
        if (e.op == Op.Nameof) { return self.checkNameOf(a, id); }
        if (e.op == Op.MacroCall) { return self.expandMacroExpr(a, id); }
        // `sizeof(T)` is a long. Its operand is the type it measures, not a value to type.
        if (e.op == Op.Sizeof) { return varType(Lit.Long, NO_SYM); }

        // The operands first: a node's type is decided from theirs. An assignment is the one place
        // the left side decides something about the right: a bare variant names no instance, and
        // the target is what says which, `m: Option<long> = mapOption(Option.None, &dbl)` is a
        // declaration written as a store, and the store is where the type is known.
        lt: VarType = self.checkExpr(a, e.left);
        rt: VarType = varType(Lit.Void, NO_SYM);
        if (e.op == Op.Assignment && lt.kind == Lit.Ref) { lt = self.lendWhole(a, e.left, lt); }
        if (e.op == Op.Assignment) {
            self.refuseStrStore(a, e.left, lt);
            rt = self.checkAimed(a, e.right, lt.structName);
            self.requireAssignable(a, lt, rt, e.right, self.placeName(a, e.left));
            if (lt.isArray) { self.requireArrayLen(a, self.placeArrayLen(a, e.left), e.right, self.placeName(a, e.left)); }
            // A borrowed view stored into a field outlives the call that lent it: the struct
            // keeps the pointer and the frame it points into is left. Building one in a struct
            // literal is a different question (there the value and the struct are made together
            // and the initializer is what the reader can see) so only the store is refused.
            if (self.unsafeDepth == 0 && a.expr(e.left).op == Op.FieldAccess
                && self.holdsView(lt.kind, lt.structName, 0)) {
                fldName: str = "this field";
                pf: Payload = a.expr(e.left).payload;
                match pf { Field(fi) { fldName = keepString(format("the field `{}`", nameOf(a.fields.get(fi).name))); } _ { } }
                failStr(format("cannot store a value of type `{}` in {}\nnote: `{}` holds a borrowed view, and a field would keep it after the call that lent it has left its frame",
                               self.spellType(lt.kind, lt.structName), fldName, self.spellType(lt.kind, lt.structName)));
            }
        } else { rt = self.checkExpr(a, e.right); }

        t: VarType = varType(e.kind, e.structName);
        p: Payload = e.payload;
        match p {
            Name(n)  {
                q: Sym = self.resolveVar(n);
                if (q != n) { a.setExpr(id, withName(e, q)); }
                if (!self.locals.has(nameOf(q))) { self.requireGlobalVisible(q); }
                t = self.lookup(q);
                // A `&self` of a scalar or a `str` receives the value itself (`lowerArg` passes an
                // argument by its own kind), so read it as that value: `self + 1` is arithmetic
                // rather than a pointer stepped by eight, and `self.len` reads the str's pair.
                // The declaration stays a borrow, which is what the convention checks ask.
                sk: Lit = scalarRefKind(t);
                if (sk != Lit.Void) {
                    t = varType(sk, NO_SYM);
                    ne: Expr = a.expr(id);
                    ne.kind = sk; ne.structName = NO_SYM;
                    a.setExpr(id, ne);
                }
                // A name nothing declares. Typing it as `void` would let `foo.bar()` on an
                // undeclared `foo` reach the assembler as a call to `mfn_bar`. A function's or a
                // type's name standing where a value is read is left to whatever reads it.
                if (t.kind == Lit.Void && !self.vars.has(nameOf(q)) && !self.fnNames.has(nameOf(n))
                    && !self.fnAt.has(nameOf(q)) && !self.fnAt.has(nameOf(n)) && !self.namesType(n)
                    && !namesScalar(nameOf(n))) {
                    failStr(format("cannot find value `{}` in this scope", nameOf(n)));
                }
                // A function's name where a value is read. A fn value is written `&name`; taken
                // bare, the name would type as nothing, pass every check, and lower as a load of
                // a global nobody declared, so a call through it would crash.
                if (t.kind == Lit.Void && e.kind != Lit.Fn && self.addrOperand != id
                    && !self.vars.has(nameOf(q)) && !self.namesType(n) && !namesScalar(nameOf(n))
                    && (self.fnNames.has(nameOf(n)) || self.fnAt.has(nameOf(q)) || self.fnAt.has(nameOf(n)))) {
                    failStr(format("`{}` is a function, not a value\nhelp: write `&{}` to use it as a fn value, or call it",
                                   nameOf(n), nameOf(n)));
                }
            }
            Sub(v)   {
                wasAddr: NodeId = self.addrOperand;
                if (e.op == Op.AddressOf) { self.addrOperand = v; }
                inner: VarType = self.checkExpr(a, v);
                self.addrOperand = wasAddr;
                // A cast to the type a value already has is the value: `"a" as str` inside a
                // typed `vec![str: ...]` is nothing at all. Between a slice and a str the cast
                // is a view over the same two words; any other cast of an aggregate is refused,
                // since a cast is a scalar conversion and lowering a struct through one reads
                // garbage.
                if (e.op == Op.Cast && (self.aggregateType(e.kind, e.structName) || self.aggregateType(inner.kind, inner.structName))) {
                    if (e.kind == inner.kind && e.structName == inner.structName) {
                        a.setExpr(id, a.expr(v));
                        return inner;
                    }
                    view: bool = (e.kind == Lit.Str || e.kind == Lit.Slice) && (inner.kind == Lit.Str || inner.kind == Lit.Slice);
                    if (!view) {
                        failStr(format("cannot cast `{}` to `{}`\nnote: a cast converts one scalar to another, and only a slice and a `str` convert between each other as views",
                                       self.spellType(inner.kind, inner.structName), self.spellType(e.kind, e.structName)));
                    }
                }
                t = self.checkSub(a, id, inner);
            }
            Call(c)  { t = self.checkCall(a, id, c); }
            Field(f) { t = self.checkField(a, f); }
            Index(i) { t = self.checkIndex(a, id, i); }
            Lit(l)   {
                if (e.op == Op.ArrayLit) {
                    failStr(stringOf("an array literal cannot be used here\nnote: an array literal `[a, b, ...]` initializes an array where one is declared (`xs: [T; N] = [...]`), or is assigned to one as a whole (`xs = [...]`)"));
                }
                self.checkLit(a, l);
                if (e.op == Op.TupleLit) { t = self.tupleOfElems(a, id, l); }
            }
            _ { }
        }
        if (e.left != NO_NODE && e.right != NO_NODE) { t = self.checkBinary(a, id, lt, rt); }

        self.stamp(a, id, t);
        return t;
    }

    // A `match` on an expression whose type the parser could not know (`match f() { ... }`). Its
    // arms were read by name, spelled `?V`, and are held to the subject's type here, where it is
    // known: each variant must be one the type has, with its payload named in full, and every
    // variant must be handled. Then each arm gets the test the parser gives a typed match.
    resolveMatch &self inout a:Ast at:long -> void {
        m: MatchNode = a.matches.get(at);
        pending: bool = false;
        for k in 0..m.armCount {
            v: Sym = a.arms.get(m.firstArm + k).variant;
            if (v != NO_SYM && strStartsWith(nameOf(v), "?")) { pending = true; }
        }
        if (!pending) { return; }
        t: VarType = self.lookup(self.resolveVar(m.scrutinee));
        owner: Sym = t.structName;
        en: long = -1;
        ti: long = -1;
        if (owner != NO_SYM) {
            en = gReg.findEnumSym(owner);
            if (en < 0) {
                r: long = gReg.findRequestSym(owner);
                if (r >= 0) { ti = gReg.findTemplateSym(gReg.requestAt(r).base); }
                if (ti < 0) { ti = gReg.templateOfInstance(nameOf(owner)); }
            }
        }
        if (en < 0 && ti < 0) {
            failStr(format("cannot `match` on a value of type `{}`\nnote: `match` reads an enum", self.spellType(t.kind, t.structName)));
        }
        backing: Lit = Lit.Int;
        hasPayload: bool = true;
        count: long = 0;
        if (en >= 0) {
            d: EnumDef = gReg.enumDef(en);
            backing = d.backing;
            hasPayload = d.hasPayload;
            count = d.variantCount;
        } else { count = gReg.templateDef(ti).variantCount; }
        shown: str = self.spellType(Lit.Struct, owner);
        covered: Vec<Sym>;
        wildcard: bool = false;
        for k in 0..m.armCount {
            arm: ArmNode = a.arms.get(m.firstArm + k);
            if (arm.variant == NO_SYM) { wildcard = true; continue; }
            vs: str = nameOf(arm.variant);
            if (strStartsWith(vs, "?")) { vs = strSlice(vs, 1, vs.len - 1); }
            vn: Sym = intern(vs);
            value: long = 0;
            arity: long = -1;
            if (en >= 0) {
                d: EnumDef = gReg.enumDef(en);
                vi: long = gReg.findVariant(d, vs);
                if (vi >= 0) { vd: VariantDef = gReg.variantAt(d, vi); value = vd.value; arity = vd.payloadCount; }
            } else {
                tp: GTemplate = gReg.templateDef(ti);
                vi: long = gReg.findGVariant(tp, vs);
                if (vi >= 0) { gv: GVariant = gReg.gVariantAt(tp, vi); value = gv.value; arity = gv.payloadCount; }
            }
            if (arity < 0) { failStr(format("no variant `{}` in enum `{}`", vs, shown)); }
            if (arity == 0 && arm.bindCount > 0) { failStr(format("variant `{}` carries no payload, so its arm binds no names", vs)); }
            if (arity != arm.bindCount && arm.bindCount < arity) {
                failStr(format("too few names for the payload of `{}`: expected {}, found {}\nhelp: name every value it carries, as `{}(...)`",
                               vs, arity, arm.bindCount, vs));
            }
            if (arity != arm.bindCount) {
                failStr(format("too many names for the payload of `{}`: expected {}, found {}", vs, arity, arm.bindCount));
            }
            covered.push(vn);
            arm.variant = vn;
            if (k + 1 < m.armCount) {
                subj: NodeId = a.leafOf(Op.Lvalue, Payload.Name(m.scrutinee), t.kind, t.structName);
                tag: NodeId = NO_NODE;
                if (en >= 0 && !hasPayload) {
                    tag = a.addExpr(Expr { op: Op.Cast, left: NO_NODE, right: NO_NODE, kind: backing,
                                           structName: NO_SYM, isParen: false, payload: Payload.Sub(subj) });
                } else {
                    a.fields.push(FieldNode { base: subj, name: intern(enumTagField()) });
                    tag = a.leafOf(Op.FieldAccess, Payload.Field(a.fields.len() - 1), Lit.Void, NO_SYM);
                }
                want: NodeId = a.leaf(Op.Literal, Payload.Num(value), backing);
                arm.test = a.binary(Op.IsEqual, tag, want, backing);
            }
            a.arms.set(m.firstArm + k, arm);
        }
        if (!wildcard) {
            for v in 0..count {
                want: Sym = NO_SYM;
                if (en >= 0) { want = gReg.variantAt(gReg.enumDef(en), v).name; }
                else { want = gReg.gVariantAt(gReg.templateDef(ti), v).name; }
                if (!symIn(covered, want)) {
                    failStr(format("`match` on `{}` does not cover `{}`\nhelp: handle every variant, or add a `_` arm",
                                   shown, nameOf(want)));
                }
            }
        }
    }

    // `operand?` is written out through the core trait `Try` (`Parser.wrapTry`), its operand held
    // in a hidden `$tryN`. Answers whether expression `id` reads that local: the local itself, or
    // a call on it (`$tryN.residual()` handed to `fromResidual`). This is what lets a failure in
    // those parts be reported as the `?` it is, rather than as calls the source never wrote.
    readsTryLocal &self inout a:Ast id:NodeId -> bool {
        if (id == NO_NODE) { return false; }
        e: Expr = a.expr(id);
        p: Payload = e.payload;
        match p {
            Name(n) { return e.op == Op.Lvalue && strStartsWith(lastComponentOf(nameOf(n)), "$try"); }
            Sub(s) { return self.readsTryLocal(a, s); }
            Call(c) { return self.readsTryLocal(a, a.calls.get(c).receiver); }
            _ { }
        }
        return false;
    }
    // `Ret.fromResidual(r)` where `r` reads a `?`'s operand: `r`, else NO_NODE.
    tryResidualArg &self inout a:Ast id:NodeId -> NodeId {
        if (id == NO_NODE) { return NO_NODE; }
        e: Expr = a.expr(id);
        if (e.op != Op.FunctionCall && e.op != Op.MethodCall) { return NO_NODE; }
        p: Payload = e.payload;
        match p {
            Call(c) {
                cn: CallNode = a.calls.get(c);
                if (cn.argCount == 1 && self.readsTryLocal(a, a.argAt(cn, 0))) { return a.argAt(cn, 0); }
            }
            _ { }
        }
        return NO_NODE;
    }
    // The operand of a `?` has no `Try` (its `isBreak` is missing).
    refuseTryOperand &self t:VarType -> never {
        failStr(format("cannot apply `?` to `{}`\nnote: `?` reads a value whose type implements `Try`, such as a `Result` or an `Option`",
                       self.spellType(t.kind, t.structName)));
    }
    // A `?`'s failure goes back as it is, so the operand's `Try` residual has to be what the return
    // type's `fromResidual` takes (`want`, Void where only the return type is known). Here the two
    // do not fit.
    refuseTryResidual &self have:VarType want:VarType -> never {
        rt: VarType = self.currentReturn;
        errs: str = "";
        if (want.kind != Lit.Void) {
            errs = keepString(format("\nnote: `{}` takes failures of type `{}`", self.spellType(rt.kind, rt.structName),
                                     self.spellType(want.kind, want.structName)));
        }
        failStr(format("`?` cannot hand back a failure of type `{}` from a function that returns `{}`{}\nnote: `?` returns the failure as it is, without converting it\nhelp: convert it to the function's failure type first",
                       self.spellType(have.kind, have.structName), self.spellType(rt.kind, rt.structName), errs));
    }

    // The local an assignment's target names, when its type is still its first store's to say.
    inferTarget &self inout a:Ast lhs:NodeId -> Sym {
        l: Expr = a.expr(lhs);
        if (l.op != Op.Lvalue) { return NO_SYM; }
        p: Payload = l.payload;
        match p { Name(n) { if (self.inferAt.has(nameOf(n))) { return n; } } _ { } }
        return NO_SYM;
    }

    // `x = v` where `x` was declared `<infer>`: `x` takes the type `v` has, and its declaration
    // says so from here on (every later pass reads the declaration). `_ = place` reads the place
    // and moves nothing out of it: an owning value is borrowed, as `match &x` borrows.
    settleInfer &self inout a:Ast id:NodeId tgt:Sym -> VarType {
        e: Expr = a.expr(id);
        at: long = self.inferAt.get(nameOf(tgt));
        self.inferAt.remove(nameOf(tgt));
        rt: VarType = self.checkExpr(a, e.right);
        discard: bool = strStartsWith(lastComponentOf(nameOf(tgt)), "$disc");
        if (rt.kind == Lit.Void) {
            if (discard) { failStr(stringOf("this expression has no value for `_ = ...` to discard")); }
            failStr(stringOf("this expression has no value to `match` on"));
        }
        if (rt.isArray) { failStr(stringOf("cannot discard or `match` on a whole array\nhelp: give it a name first, and use that")); }
        // A `&self` of a scalar or a `str` is the value (`scalarRefKind`); a literal its type.
        if (scalarRefKind(rt) != Lit.Void) { rt = varType(scalarRefKind(rt), NO_SYM); }
        d: VarDeclNode = a.decls.get(at);
        d.kind = rt.kind;
        d.structName = rt.structName;
        ro: Op = a.expr(e.right).op;
        if (discard && rt.kind == Lit.Struct && gReg.needsDrop(rt.structName)
            && (ro == Op.Lvalue || ro == Op.FieldAccess || ro == Op.ArrayIndex || ro == Op.Deref)) {
            d.kind = Lit.Ref;
            e.right = a.leafOf(Op.AddressOf, Payload.Sub(e.right), Lit.Ref, rt.structName);
        }
        a.decls.set(at, d);
        t: VarType = varType(d.kind, d.structName);
        hit: Option<long> = self.vars.find(nameOf(tgt));
        match hit { Some(i) { self.types.set(i, t); } None { } }
        le: Expr = a.expr(e.left);
        le.kind = t.kind;
        le.structName = t.structName;
        a.setExpr(e.left, le);
        e.kind = t.kind;
        e.structName = t.structName;
        a.setExpr(id, e);
        return t;
    }

    // `p = v` where `p` is a lent parameter (`inout p:T`, a `&self` receiver): the store writes the
    // caller's value, as `p.x = v` writes the caller's field. The target becomes `*p`
    // (`lentPlaceOf`), typed as the value, and from there every pass treats it as a store to a
    // place: the old value is released after the new one is built, the new one is moved in, and a
    // borrow on the right is copied from, or refused when it owns something. Without this, the
    // store would re-aim the parameter's own pointer and the caller would see nothing. A `&self`
    // of a scalar (a backed enum, a distinct type) receives the value itself, so there is no
    // caller's value to write and the store is refused. A borrow the function declares for itself
    // (a `for x in &xs` element, a match binding through a borrow, an `unsafe` `&T` local) keeps
    // its own rules.
    //
    // A struct a closure captured is a lent place too: the closure holds a borrow of it in the
    // field `__cl.t`, so `t = v` in the body writes the variable it was built over, as `t.x = v`
    // does, and not the closure's own pointer.
    lendWhole &self inout a:Ast id:NodeId lt:VarType -> VarType {
        e: Expr = a.expr(id);
        if (self.curFn < 0) { return lt; }
        n: Sym = NO_SYM;
        match e.payload { Name(x) { if (e.op == Op.Lvalue) { n = x; } } _ { } }
        lent: bool = false;
        if (n == NO_SYM) {
            if (!self.captureField(a, id) || lt.structName == NO_SYM) { return lt; }
            lent = true;
            match e.payload { Field(i) { n = a.fields.get(i).name; } _ { } }
        }
        f: FnNode = a.fns.get(self.curFn);
        k: long = 0;
        while (k < f.argCount && !lent) {
            p: VarDeclNode = a.paramAt(f, k);
            lent = p.name == n && p.conv == Conv.Inout && p.kind == Lit.Ref;
            k = k + 1;
        }
        if (!lent) { return lt; }
        if (namedScalar(Lit.Struct, lt.structName)) {
            failStr(format("cannot assign to `{}`\nnote: a `&self` of `{}` receives the value itself (it is a scalar), so the store would change only this call's copy\nhelp: return the new value instead",
                           nameOf(n), self.spellType(Lit.Struct, lt.structName)));
        }
        inner: NodeId = a.addExpr(e);
        a.setExpr(id, Expr { op: Op.Deref, left: NO_NODE, right: NO_NODE, kind: Lit.Struct,
                             structName: lt.structName, isParen: false, payload: Payload.Sub(inner) });
        return varType(Lit.Struct, lt.structName);
    }

    // `self = v` in a `&self` method of a scalar or a `str`: the method holds the value itself,
    // so the store would change only its own copy. Refused as `lendWhole` refuses it for a
    // backed enum; asked before the target is typed, which reads it as that value.
    refuseScalarSelfStore &self inout a:Ast lhs:NodeId -> void {
        if (lhs == NO_NODE) { return; }
        e: Expr = a.expr(lhs);
        if (e.op != Op.Lvalue) { return; }
        n: Sym = NO_SYM;
        match e.payload { Name(x) { n = x; } _ { return; } }
        t: VarType = self.lookup(self.resolveVar(n));
        if (scalarRefKind(t) == Lit.Void) { return; }
        failStr(format("cannot assign to `{}`\nnote: a `&self` of `{}` receives the value itself (it is a scalar), so the store would change only this call's copy\nhelp: return the new value instead",
                       nameOf(n), typeName(scalarRefKind(t))));
    }

    // A struct literal's field values. They are expressions like any other and nothing else
    // reaches them, so a call written here would otherwise never be rewritten into the ordinary
    // call it has to become. Each is checked against the field it initializes, which is what
    // settles a variant constructor's instance and boxes a concrete value into a trait field.
    checkLit &self inout a:Ast at:long -> void {
        n: LitNode = a.lits.get(at);
        // A closure literal's initializers are not the author's: the parser wrote them, and a
        // scalar capture is `&x` (a raw address) because that is how a write inside the closure
        // reaches the original. Trusted, as the body's reads through them are (`captureRead`).
        if (isClosureStruct(n.typeName)) {
            self.unsafeDepth = self.unsafeDepth + 1;
            self.checkLitFields(a, at);
            self.unsafeDepth = self.unsafeDepth - 1;
            return;
        }
        self.checkLitFields(a, at);
    }

    checkLitFields &self inout a:Ast at:long -> void {
        n: LitNode = a.lits.get(at);
        si: long = gReg.findStructSym(n.typeName);
        // `..rest` supplies every field not named, so the count is not the question, where the
        // rest come from is. It is a copy, so a type that owns something is refused.
        if (n.rest != NO_NODE) {
            if (si >= 0 && gReg.structDef(si).isEnum) {
                failStr(format("cannot use `..` in a literal of the sum type `{}`\nnote: a value of a sum type holds one variant, so there are no remaining fields to fill",
                               nameOf(n.typeName)));
            }
            // `..` copies the fields it was not given, and a type that owns something cannot be
            // copied that way: the base and the new value would both release the same buffer.
            if (gReg.needsDrop(n.typeName)) {
                failStr(format("cannot copy the remaining fields of `{}` with `..`\nnote: `{}` owns something, and the base and the new value would both release it\nhelp: name every field, or clone the base first",
                               nameOf(n.typeName), nameOf(n.typeName)));
            }
            r: VarType = self.checkExpr(a, n.rest);
            if (!(r.kind == Lit.Struct || r.kind == Lit.Ref) || r.structName != n.typeName) {
                failStr(format("mismatched types: expected `{}`, found `{}`\nnote: `..` takes the remaining fields from a value of the literal's own type",
                               nameOf(n.typeName), self.spellType(r.kind, r.structName)));
            }
        }
        k: long = 0;
        if (si < 0) {                       // a template not yet aimed at an instance
            while (k < n.initCount) {
                self.checkExpr(a, a.inits.get(n.firstInit + k).value);
                k = k + 1;
            }
            return;
        }
        d: StructDef = gReg.structDef(si);
        while (k < n.initCount) {
            iv: InitNode = a.inits.get(n.firstInit + k);
            fi: long = gReg.findFieldSym(d, iv.name);
            if (fi < 0) { self.checkExpr(a, iv.value); k = k + 1; continue; }
            f: FieldDef = gReg.fieldAt(d, fi);
            // `S { xs: [a, b, c] }`: an array field takes an array literal naming every element,
            // each held to the element type as a store to one is.
            if (f.isArray && a.expr(iv.value).op == Op.ArrayLit) {
                self.checkArrayLitInto(a, iv.value, f);
                k = k + 1;
                continue;
            }
            vt: VarType = self.checkAimed(a, iv.value, f.structName);
            // Held to the field's type as a store to it is. Otherwise a `Node` where a `Box<Node>`
            // is declared would be accepted, and the box's pointer would read the node's first
            // word. A closure's captures are the parser's (`&x` into a `&T` field) and are not
            // asked.
            if (!isClosureStruct(n.typeName)) {
                self.requireAssignable(a, VarType { kind: f.kind, structName: f.structName, isArray: f.isArray },
                                       vt, iv.value, litFieldWhat(f.name));
                if (f.isArray) { self.requireArrayLen(a, f.count, iv.value, litFieldWhat(f.name)); }
            }
            if (f.kind == Lit.TraitObj && a.expr(iv.value).kind == Lit.Struct) {
                self.aimTraitObj(a, a.expr(iv.value).structName, f.structName);
                a.inits.set(n.firstInit + k,
                            InitNode { name: iv.name,
                                       value: a.leafOf(Op.MakeTraitObj, Payload.Sub(iv.value),
                                                       Lit.TraitObj, f.structName) });
            }
            k = k + 1;
        }
        if (n.rest == NO_NODE && n.initCount < d.fieldCount && !d.isEnum
            && !isClosureStruct(n.typeName) && !isTupleName(n.typeName)) {
            self.fillOmitted(a, at, d);
        }
    }

    // An array literal for the array field `f` of a struct literal: every element given, as a
    // declaration's literal must, each held to the element type. The literal is typed by its
    // element, as a global's is, which is what the lowerer (`lowerArrayInto`) and the evaluator
    // (`buildArray`) build it from.
    checkArrayLitInto &self inout a:Ast lit:NodeId f:FieldDef -> void {
        e: Expr = a.expr(lit);
        ln: LitNode = a.lits.get(0);
        match e.payload { Lit(l) { ln = a.lits.get(l); } _ { } }
        if (ln.initCount != f.count) {
            failStr(format("wrong number of elements in an array literal: expected {}, found {}\nnote: an array literal names every element of the array",
                           f.count, ln.initCount));
        }
        for j in 0..ln.initCount {
            v: NodeId = a.inits.get(ln.firstInit + j).value;
            self.requireAssignable(a, varType(f.kind, f.structName), self.checkAimed(a, v, f.structName), v,
                                   keepString(format("element {} of field `{}`", j, nameOf(f.name))));
        }
        e.kind = f.kind;
        e.structName = f.structName;
        a.setExpr(lit, e);
    }

    // A literal that leaves fields out. Zero bytes are a value for a scalar, a view, an array, a
    // struct that owns nothing and a sum type whose zero is a variant with no payload (`Option`'s
    // is `None`), and those stay zero-filled. An omitted field whose type implements `Default`
    // gets its default (`T.new()`, an initializer of its own). One that owns a resource and has no
    // default is refused: a zeroed `File` would be fd 0, and releasing it would close stdin.
    fillOmitted &self inout a:Ast at:long d:StructDef -> void {
        n: LitNode = a.lits.get(at);
        extra: Vec<InitNode>;
        for k in 0..d.fieldCount {
            f: FieldDef = gReg.fieldAt(d, k);
            if (f.isArray || f.kind != Lit.Struct || f.structName == NO_SYM) { continue; }
            if (namedScalar(f.kind, f.structName)) { continue; }
            named: bool = false;
            j: long = 0;
            while (j < n.initCount && !named) {
                named = a.inits.get(n.firstInit + j).name == f.name;
                j = j + 1;
            }
            if (named || zeroIsEmptyVariant(f.structName)) { continue; }
            ctor: Sym = methodSymbol(f.structName, intern("new"));
            if (gReg.structImplements(nameOf(f.structName), intern("Default")) && self.fnNames.has(nameOf(ctor))) {
                a.calls.push(CallNode { name: self.resolveFn(ctor), receiver: NO_NODE,
                                        firstArg: 0, argCount: 0, slot: NO_SLOT, callee: NO_NODE, sigKey: NO_SYM });
                v: NodeId = a.leafOf(Op.FunctionCall, Payload.Call(a.calls.len() - 1), Lit.Struct, f.structName);
                self.checkExpr(a, v);
                extra.push(InitNode { name: f.name, value: v });
            } else if (gReg.needsDrop(f.structName)) {
                failStr(format("missing field `{}` of type `{}`\nnote: `{}` owns a resource and has no default, so the field cannot be left out",
                               fieldSpelling(f.name), self.spellType(Lit.Struct, f.structName), self.spellType(Lit.Struct, f.structName)));
            }
        }
        if (extra.len() == 0) { return; }
        first: long = a.inits.len();
        for j in 0..n.initCount { a.inits.push(a.inits.get(n.firstInit + j)); }
        a.inits.extend(extra);
        a.lits.set(at, LitNode { typeName: n.typeName, firstInit: first, initCount: n.initCount + extra.len(),
                                 rest: n.rest });
    }

    stamp &self inout a:Ast id:NodeId t:VarType -> void {
        e: Expr = a.expr(id);
        e.kind = t.kind;
        e.structName = t.structName;
        a.setExpr(id, e);
    }

    // Reading or writing memory the compiler cannot vouch for (a raw pointer, a raw address, an
    // `asm` block, a call to an `unsafe` function) is only legal inside an `unsafe { }` block or
    // the body of an `unsafe` function. That boundary is what every other safety rule in the
    // language rests on: outside it the checker answers for the program, and inside it the author
    // does. An `unsafe` function's whole body is one such region from its first statement.
    requireUnsafe &self what:str -> void {
        if (self.unsafeDepth > 0) { return; }
        s: String;
        s.pushStr(what);
        s.pushStr(" is only allowed in an `unsafe` block or function");
        failStr(s);
    }

    // `*__cl.n` in a closure's `call`: the parser's read of a scalar it captured by pointer
    // (`Parser.captureOf`), through the receiver it declared. The field holds the address of a
    // variable the closure was built over, so the read is the compiler's, not the author's, and
    // safe code may hold it. The receiver is known by being the call's first parameter with the
    // capture struct's type: a local of that name in safe code could not hold that borrow.
    captureRead &self inout a:Ast id:NodeId -> bool {
        v: NodeId = NO_NODE;
        match a.expr(id).payload { Sub(x) { v = x; } _ { return false; } }
        return self.captureField(a, v);
    }

    // `__cl.x` in a closure's `call`: a capture, read off the receiver the parser declared.
    captureField &self inout a:Ast id:NodeId -> bool {
        if (self.curFn < 0 || id == NO_NODE) { return false; }
        fe: Expr = a.expr(id);
        if (fe.op != Op.FieldAccess) { return false; }
        base: NodeId = NO_NODE;
        match fe.payload { Field(i) { base = a.fields.get(i).base; } _ { return false; } }
        be: Expr = a.expr(base);
        if (be.op != Op.Lvalue) { return false; }
        n: Sym = NO_SYM;
        match be.payload { Name(x) { n = x; } _ { return false; } }
        f: FnNode = a.fns.get(self.curFn);
        if (f.argCount == 0 || a.paramAt(f, 0).name != n || !isClosureCall(f.name)) { return false; }
        t: VarType = self.lookup(n);
        return t.kind == Lit.Ref && isClosureStruct(t.structName);
    }

    // An `unsafe` function may only be called from an unsafe context. That is what declaring one
    // `unsafe` means, and it applies to methods too, which reach here as ordinary calls.
    //
    // A closure's `call` is the exception. It is `unsafe` only when it was written inside
    // `unsafe` code, whose author vouched for its body where it stands; whoever is handed the
    // closure calls it as any other.
    requireSafeCallee &self inout a:Ast fn:Sym -> void {
        if (isClosureCall(fn)) { return; }
        at: long = self.fnNodeOf(fn);
        if (at < 0 || !a.fns.get(at).isUnsafe) { return; }
        s: String;
        s.pushStr("calling the unsafe function `");
        s.pushStr(nameOf(fn));
        s.push('`');
        self.requireUnsafe(keepString(s));
    }

    // The function `&f` names, after `addressedFn` has resolved it onto the node.
    addressedName &self inout a:Ast id:NodeId -> Sym {
        p: Payload = a.expr(id).payload;
        inner: NodeId = NO_NODE;
        match p { Sub(v) { inner = v; } _ { return NO_SYM; } }
        if (inner == NO_NODE) { return NO_SYM; }
        q: Payload = a.expr(inner).payload;
        match q { Name(x) { return x; } _ { } }
        return NO_SYM;
    }

    // A value in memory, as a cast sees it: a struct, a str or a slice. A backed enum is not one:
    // it is `Struct`-kinded but a scalar underneath, and casts to its backing integer.
    aggregateType &self k:Lit n:Sym -> bool {
        if (!isAggregate(k)) { return false; }
        // A backed enum is its backing integer and casts like one. A sum type is not: it is a tag
        // and a payload, and casting one to an integer would read its tag by accident. That is
        // why this asks `isBackedEnum` and not `findEnum`, which would let `Shape.Empty as long`
        // through.
        if (k == Lit.Struct && isBackedEnum(n)) { return false; }
        return true;
    }

    // A prefix operator, a cast, or a dereference.
    checkSub &self inout a:Ast id:NodeId inner:VarType -> VarType {
        e: Expr = a.expr(id);
        if (e.op == Op.Cast) {
            // A float converts to and from any integer and the other float width, and to nothing
            // else: there is no bool, address or aggregate a float's value is.
            fromK: Lit = storedKind(inner.kind, inner.structName);
            if (scalarRefKind(inner) != Lit.Void) { fromK = scalarRefKind(inner); }
            toK: Lit = storedKind(e.kind, e.structName);
            if ((isFloat(fromK) || isFloat(toK)) && !((isFloat(fromK) || isInteger(fromK)) && (isFloat(toK) || isInteger(toK)))) {
                failStr(format("cannot cast `{}` to `{}`\nnote: a float converts only to and from the integers and the other float width",
                               self.spellType(inner.kind, inner.structName), self.spellType(e.kind, e.structName)));
            }
            // A fn value made of a raw word (a vtable slot read through a pointer, as `fmt.k`'s
            // `callDisplay` does): its type is noted, since a call through one may reach any
            // implementation the compiler placed in a vtable (`ConstGuard.rawFits`).
            if (e.kind == Lit.Fn && inner.kind != Lit.Fn && e.structName != NO_SYM) { gRawFnSigs.push(e.structName); }
            return varType(e.kind, e.structName);
        }
        // `&name` of a function is a function pointer, not an address: it is what a `fn` variable
        // holds and what an `Fn` bound is inferred from. `&x` of a variable is still an address.
        if (e.op == Op.AddressOf) {
            fs: Sym = self.addressedFn(a, id);
            if (fs != NO_SYM) {
                gAddressedFns.push(self.addressedName(a, id));
                gAddressedSigs.push(fs);
                // A global's initializer is in no body the convention walk judges, so its `&f`
                // is kept for `enforceGlobalFnRefs`.
                if (self.curFn < 0) { self.globalFnRefs.push(id); self.globalFnRefPos.push(gPos); }
                // A safe caller could otherwise smuggle an unsafe function out through a pointer.
                at: long = self.fnNodeOf(self.addressedName(a, id));
                if (at >= 0 && a.fns.get(at).isUnsafe) {
                    self.requireUnsafe("taking a pointer to an unsafe function");
                }
                return varType(Lit.Fn, fs);
            }
            // `&x` of a struct, of a struct field, of a struct element, and `&a[..]` are lends:
            // safe code's way of handing something over without giving it away. Everything else
            // it can be written on (a scalar, an array, a `str`, a slice's bytes) is a raw
            // 64-bit address, and a raw address is the author's word, not the checker's.
            // An array in safe code is lent as its elements, to a slice parameter (`decayArrayLend`
            // rewrites `&arr` there into `&arr[..]`); anywhere else it is said what to write.
            if (inner.isArray && self.unsafeDepth == 0) {
                failStr(stringOf("cannot lend a whole array here\nnote: `&` of an array lends its elements to a slice parameter (`inout xs:[T]`), as `&xs[..]`, and a type parameter or a struct cannot stand for an array\nhelp: wrap the array in a struct to lend it whole, or take its raw address inside `unsafe`"));
            }
            if (!(inner.kind == Lit.Struct || inner.kind == Lit.Ref || inner.kind == Lit.Slice)
                || inner.isArray) {
                // `&n` handed straight to a call: a lend if the parameter is an `inout` scalar,
                // which is known once the callee is (`holdScalarLends`).
                if (self.lendingArg == id && self.unsafeDepth == 0 && !inner.isArray) {
                    self.scalarLends.push(id);
                    return varType(Lit.Long, NO_SYM);
                }
                self.requireUnsafe("taking a raw address with `&`");
            }
            return varType(Lit.Long, NO_SYM);
        }
        // `~x` and `!x` on an aggregate. Left alone, both would fall through to the machine
        // operation on the pointer an aggregate flows as: `~s` would complement the ADDRESS and
        // hand the result back typed as the struct. `~` answers to a trait like every other
        // operator; `!` does not, because it asks whether a truth value is false, and a block of
        // bytes has none to ask about.
        if (e.op == Op.BitwiseNot && comparedByCall(underBorrow(inner))) {
            return self.rewriteToNot(a, id, inner);
        }
        if (e.op == Op.LogicalNot && comparedByCall(underBorrow(inner))) {
            failStr(format("cannot apply `!` to `{}`\nnote: `{}` has no truth value\nhelp: compare it, or call something that answers one",
                           typeMangleName(inner.kind, inner.structName), typeMangleName(inner.kind, inner.structName)));
        }
        if ((e.op == Op.LogicalNot || e.op == Op.BitwiseNot) && isFloat(inner.kind)) {
            failStr(format("cannot apply `{}` to `{}`\nhelp: compare it instead, as in `x == 0.0`", opName(e.op), typeName(inner.kind)));
        }
        // `!b` of a `bool` (or of a truth value: a comparison, `&&`, `||`, another `!`) is a
        // `bool`. Of an integer it is still "is zero", a 0/1 `int`.
        if (e.op == Op.LogicalNot) {
            inn: Expr = a.expr(id);
            p: Payload = e.payload;
            match p { Sub(v) { inn = a.expr(v); } _ { } }
            if (inner.kind == Lit.Bool || isTruthValue(inn.kind, inn.op)) { return varType(Lit.Bool, NO_SYM); }
            return varType(Lit.Int, NO_SYM);
        }
        if (e.op == Op.Deref) {
            // `*p` of a lent parameter: what `lendWhole` writes, read again by a later round.
            if (lentPlaceOf(a, id) != NO_NODE && e.kind == Lit.Struct && e.structName != NO_SYM
                && !namedScalar(Lit.Struct, e.structName)) {
                return varType(Lit.Struct, e.structName);
            }
            // `x` of `inout x:long`: the caller's scalar, read and written where it lies.
            if (lentPlaceOf(a, id) != NO_NODE && inner.kind == Lit.Ref && isInoutScalarName(inner.structName)) {
                st: TypeRef = inoutScalarOf(inner.structName);
                return varType(st.base, st.name);
            }
            if (!self.captureRead(a, id)) { self.requireUnsafe("dereferencing a raw pointer"); }
            // `*p` yields the pointee, which the pointer's companion name records: as the
            // spelling the mangler produced, so `**T` peels to a `*T` rather than to a struct
            // called `ptr_T`.
            if (inner.kind == Lit.Ptr && inner.structName != NO_SYM) {
                pointee: TypeRef = unmangledType(nameOf(inner.structName));
                return varType(pointee.base, pointee.name);
            }
            return varType(Lit.Long, NO_SYM);
        }
        return inner;
    }

    // Two operands meet at the wider type; a comparison yields a bool whatever they were.
    checkBinary &self inout a:Ast id:NodeId lt0:VarType rt0:VarType -> VarType {
        e: Expr = a.expr(id);
        lt: VarType = lt0;
        rt: VarType = rt0;
        // An aggregate has no machine comparison: equality for a block of bytes is a question
        // only the type can answer, so `==` on one means whatever its `Eq` says it means. Only
        // the two equality operators dispatch: ordering is a separate contract and would be a
        // separate trait.
        // A borrow of an aggregate is the aggregate here: `a == b` of two `&P` is P's `Eq`, not a
        // comparison of the addresses the borrows hold.
        if ((e.op == Op.IsEqual || e.op == Op.IsNotEqual)
            && (comparedByCall(underBorrow(lt)) || comparedByCall(underBorrow(rt)))) {
            return self.rewriteToEq(a, id, lt, rt);
        }
        // An aggregate has no machine arithmetic either, so `+` on one means whatever its type
        // says it means: a call to `Add::add`. Only addition dispatches: the others have no
        // meaning worth guessing at, and a type that wants one can say so when there is a trait
        // for it. Left as a machine add, `s + "x"` on a String would add two addresses and read
        // the result as a String.
        if (opTraitName(e.op).len > 0 && (isAggregate(underBorrow(lt).kind) || isAggregate(underBorrow(rt).kind))) {
            return self.rewriteToOperator(a, id, lt, rt, opTraitName(e.op));
        }
        // Ordering an aggregate is the same story as equality: there is no machine answer for a
        // block of bytes, so `<` means whatever the type's `Ord` says it means. Left alone it would
        // fall through to the integer compare below, which on an aggregate compares the POINTERS
        // the operands flow as: two structs with identical fields would report an order, and
        // which one came first would depend on where they sat in the frame.
        if (isRelational(e.op) && (comparedByCall(underBorrow(lt)) || comparedByCall(underBorrow(rt)))) {
            return self.rewriteToOrd(a, id, lt, rt);
        }
        // A comparison computes an int and means a bool. It is typed as what it computes, because
        // that is the width its result is stored at, and the places that want the meaning (a
        // `bool` annotation, an inferred return, an `Fn(..) -> bool` bound) convert it there.
        // Typed `bool` here, it would be written as one byte where four are read.
        // A float meets only a float of its own width. A literal on one side takes the other's
        // (`x < 1.5` with `x: f32`); `-x` is the parser's `0 - x` with the zero marked, and over a
        // float it is a negation, not a subtraction from an integer. A borrow of a float (`self`
        // in `methods f64`) is the float.
        if (scalarRefKind(lt) != Lit.Void && isFloat(scalarRefKind(lt))) { lt = varType(scalarRefKind(lt), NO_SYM); }
        if (scalarRefKind(rt) != Lit.Void && isFloat(scalarRefKind(rt))) { rt = varType(scalarRefKind(rt), NO_SYM); }
        if (e.op != Op.Assignment && e.op != Op.LogicalAnd && e.op != Op.LogicalOr
            && (isFloat(lt.kind) || isFloat(rt.kind))) {
            if (e.op == Op.Subtraction && isFloat(rt.kind) && self.isNegationZero(a, e.left)) {
                self.retypeLeaf(a, e.left, rt.kind);
                return varType(rt.kind, NO_SYM);
            }
            if (self.adoptFloat(a, e.right, lt.kind)) { rt = varType(lt.kind, NO_SYM); }
            if (self.adoptFloat(a, e.left, rt.kind)) { lt = varType(rt.kind, NO_SYM); }
            if (lt.kind != rt.kind) {
                failStr(format("cannot apply `{}` to `{}` and `{}`\nnote: a float meets only a float of its own width\nhelp: convert one of them with `as`",
                               opName(e.op), self.spellType(lt.kind, lt.structName), self.spellType(rt.kind, rt.structName)));
            }
            if (e.op == Op.Modulus || e.op == Op.BitwiseAnd || e.op == Op.BitwiseOr || e.op == Op.BitwiseXor
                || e.op == Op.ShiftLeft || e.op == Op.ShiftRight) {
                failStr(format("cannot apply `{}` to `{}`\nnote: a float has `+`, `-`, `*`, `/` and the comparisons",
                               opName(e.op), self.spellType(lt.kind, lt.structName)));
            }
        }
        // A shift is computed at its left operand's type, whatever the count's: `h >> k` with
        // `h: u64` and `k: long` is a `u64`, `b << 4` with `b: u8` a `u8`. A literal on the left
        // has no type of its own to give, and takes the count's where that is wider than an
        // `int` (`1 << k` is a `long` for `k: long`, an `int` for `k: int`), or a wider one that
        // what it meets or is stored in asks for (`adoptWide`: `m: long = 1 << k`).
        if ((e.op == Op.ShiftLeft || e.op == Op.ShiftRight) && isInteger(lt.kind) && isInteger(rt.kind)) {
            if (self.weakArg(a, e.left) && !self.weakArg(a, e.right)) {
                k: Lit = higherPrecedence(lt.kind, rt.kind);
                if (noCommonType(lt.kind, rt.kind)) { k = rt.kind; }
                if (k != lt.kind && typeInfo(k).size > typeInfo(lt.kind).size) {
                    match self.weakValue(a, e.left) {
                        Some(v) { if (literalFits(v, k)) { self.retypeIntTree(a, e.left, k); return varType(k, NO_SYM); } }
                        None { }
                    }
                }
            }
            return lt;
        }
        // Literal arithmetic meeting an 8-byte integer is computed at its width (`adoptWide`).
        if (e.op != Op.Assignment && e.op != Op.LogicalAnd && e.op != Op.LogicalOr) {
            if (self.adoptWide(a, e.right, lt.kind)) { rt = varType(lt.kind, NO_SYM); }
            if (self.adoptWide(a, e.left, rt.kind)) { lt = varType(rt.kind, NO_SYM); }
        }
        // A literal operand takes the other operand's type when its value is one of that type's:
        // `b + 1` with `b: u8` is a `u8`, `h * 31` with `h: u64` a `u64`, `x < 0` with `x: u32`
        // compares two `u32`s. One that is not keeps its own and meets as any operand does
        // (`b + 300` is an `int`, and `h == -1` meets no type).
        if (e.op != Op.Assignment && e.op != Op.LogicalAnd && e.op != Op.LogicalOr
            && isInteger(lt.kind) && isInteger(rt.kind)) {
            if (self.adoptLiteral(a, e.right, rt.kind, e.left, lt.kind)) { rt = varType(lt.kind, NO_SYM); }
            else if (self.adoptLiteral(a, e.left, lt.kind, e.right, rt.kind)) { lt = varType(rt.kind, NO_SYM); }
            if (noCommonType(lt.kind, rt.kind)) {
                failStr(format("cannot apply `{}` to `{}` and `{}`\nnote: no integer type holds both\nhelp: say which one is meant with `as` (`x as long`, `n as u64`)",
                               opName(e.op), typeName(lt.kind), typeName(rt.kind)));
            }
        }
        if (isComparison(e.op)) { return varType(Lit.Int, NO_SYM); }
        if (e.op == Op.LogicalAnd || e.op == Op.LogicalOr) {
            return varType(Lit.Int, NO_SYM);
        }
        if (e.op == Op.Assignment) { return lt; }
        if (lt.kind == Lit.Struct || lt.kind == Lit.Ref) { return lt; }
        return varType(higherPrecedence(lt.kind, rt.kind), lt.structName);
    }

    // `a == b` on an aggregate, as the call it means. Dispatch is by bound, not through a vtable:
    // both operand types are known here, so the call is direct and the inliner can erase it. An
    // operator costs exactly what writing the method call by hand costs. `a != b` becomes
    // `!a.eq(b)`: one contract, with no way for the two to disagree.
    rewriteToEq &self inout a:Ast id:NodeId lt0:VarType rt0:VarType -> VarType {
        lt: VarType = underBorrow(lt0);
        rt: VarType = underBorrow(rt0);
        owner: Sym = self.eqOwner(lt);
        fn: Sym = NO_SYM;
        if (owner != NO_SYM) { fn = self.eqMethodOf(owner, rt); }
        // Not implemented, but equality between two values of the same type can be derived field
        // by field, and is, the first time something asks for it. Only `Eq`: what `==` means field
        // by field is obvious, what `+` would mean is not.
        if (fn == NO_SYM && lt.kind == Lit.Struct && rt.kind == Lit.Struct
            && lt.structName == rt.structName && !gReg.isDistinct(lt.structName)
            && self.deriveEq(a, lt.structName)) {
            fn = self.eqMethodOf(owner, rt);
        }
        if (fn == NO_SYM) {
            failStr(format("cannot compare `{}` with `{}`{}\nhelp: implement `Eq<{}>` for `{}`, or compare their fields",
                           typeMangleName(lt.kind, lt.structName), typeMangleName(rt.kind, rt.structName), distinctHint(lt),
                           typeMangleName(rt.kind, rt.structName), typeMangleName(lt.kind, lt.structName)));
        }
        e: Expr = a.expr(id);
        c: long = self.eqCall(a, fn, e.left, e.right);
        ret: VarType = self.returnOf(fn);
        if (e.op == Op.IsEqual) {
            a.setExpr(id, Expr { op: Op.MethodCall, left: NO_NODE, right: NO_NODE, kind: ret.kind,
                                 structName: ret.structName, isParen: e.isParen,
                                 payload: Payload.Call(c) });
            return ret;
        }
        call: NodeId = a.leafOf(Op.MethodCall, Payload.Call(c), ret.kind, ret.structName);
        a.setExpr(id, Expr { op: Op.LogicalNot, left: NO_NODE, right: NO_NODE, kind: Lit.Int,
                             structName: NO_SYM, isParen: e.isParen, payload: Payload.Sub(call) });
        return varType(Lit.Int, NO_SYM);
    }

    // The `cmp` a type implements. A parameterized trait puts its instantiation in the method's
    // name, which is what lets one type be `Eq` at several; `Ord` takes no parameters, so it
    // contributes no segment at all and its method is named off the type alone: `long_cmp`, not
    // `long_Ord_cmp`. That is also why this cannot tell an `Ord` implementation from an inherent
    // `cmp` of the same shape, and does not try to: the name is the contract here, as it is for
    // every other non-parameterized trait.
    ordMethodOf &self owner:Sym -> Sym { return self.bareMethodOf(owner, "cmp"); }

    // The method a type implements a NON-parameterized trait with. Such a trait contributes no
    // segment to the mangling, so its method is named off the type alone: `long_cmp`, `V_not`.
    bareMethodOf &self owner:Sym method:str -> Sym {
        if (owner == NO_SYM) { return NO_SYM; }
        cand: Sym = methodSymbol(owner, intern(method));
        if (self.fnNames.has(nameOf(cand))) { return self.resolveFn(cand); }
        return NO_SYM;
    }

    // `~a` on an aggregate, as the call it means: `a.not()`.
    rewriteToNot &self inout a:Ast id:NodeId t0:VarType -> VarType {
        t: VarType = underBorrow(t0);
        fn: Sym = self.bareMethodOf(self.eqOwner(t), "not");
        if (fn == NO_SYM) {
            failStr(format("cannot apply `~` to `{}`\nhelp: implement `Not` for `{}`, or write the operation out",
                           typeMangleName(t.kind, t.structName), typeMangleName(t.kind, t.structName)));
        }
        e: Expr = a.expr(id);
        operand: NodeId = NO_NODE;
        p: Payload = e.payload;
        match p { Sub(v) { operand = v; } _ { } }
        args: Vec<NodeId>;
        a.calls.push(CallNode { name: fn, receiver: operand, firstArg: a.addArgs(args),
                                argCount: 0, slot: NO_SLOT, callee: NO_NODE, sigKey: NO_SYM });
        ret: VarType = self.returnOf(fn);
        a.setExpr(id, Expr { op: Op.MethodCall, left: NO_NODE, right: NO_NODE, kind: ret.kind,
                             structName: ret.structName, isParen: e.isParen,
                             payload: Payload.Call(a.calls.len() - 1) });
        return ret;
    }

    // `a < b` on an aggregate, as the call it means: `a.cmp(b) < 0`. The operator is kept and only
    // its operands change, so `<=` and `>` need no cases of their own and the result is still the
    // integer compare the rest of the checker expects.
    //
    // Not derived the way `==` is. What equality means field by field is obvious; what ORDER means
    // is a choice only the type can make, and guessing at declaration order would be a silent
    // answer to a question the program did not ask.
    rewriteToOrd &self inout a:Ast id:NodeId lt0:VarType rt0:VarType -> VarType {
        lt: VarType = underBorrow(lt0);
        rt: VarType = underBorrow(rt0);
        owner: Sym = self.eqOwner(lt);
        fn: Sym = self.ordMethodOf(owner);
        if (fn == NO_SYM || lt.kind != rt.kind || lt.structName != rt.structName) {
            failStr(format("cannot order values of type `{}`{}\nhelp: implement `Ord` for `{}`, or compare their fields",
                           typeMangleName(lt.kind, lt.structName), distinctHint(lt), typeMangleName(lt.kind, lt.structName)));
        }
        e: Expr = a.expr(id);
        c: long = self.eqCall(a, fn, e.left, e.right);
        ret: VarType = self.returnOf(fn);
        call: NodeId = a.leafOf(Op.MethodCall, Payload.Call(c), ret.kind, ret.structName);
        zero: NodeId = a.leaf(Op.Literal, Payload.Num(0), ret.kind);
        a.setExpr(id, Expr { op: e.op, left: call, right: zero, kind: Lit.Int,
                             structName: NO_SYM, isParen: e.isParen, payload: Payload.None });
        return varType(Lit.Int, NO_SYM);
    }

    // `a + b` on an aggregate, as the call it means. Dispatch is by bound, not through a vtable:
    // both operand types are known here, so the call is direct and the inliner can erase it. An
    // operator costs exactly what writing the method call by hand costs. `add` takes `self` by
    // value, so `s + "x"` hands `s` over and gets the grown buffer back: that move is what makes
    // a chain cost one allocation's growth instead of a whole String per step, and it is why
    // using `s` afterwards is a compile error rather than a stale read.
    rewriteToOperator &self inout a:Ast id:NodeId lt0:VarType rt0:VarType trait:str -> VarType {
        lt: VarType = underBorrow(lt0);
        rt: VarType = underBorrow(rt0);
        owner: Sym = self.eqOwner(lt);
        fn: Sym = NO_SYM;
        if (owner != NO_SYM) { fn = self.opMethodOf(owner, rt, trait, lowerOf(trait)); }
        if (fn == NO_SYM) {
            hint: str = distinctHint(lt);
            if (hint.len == 0) { hint = distinctHint(rt); }
            failStr(format("cannot apply `{}` to `{}` and `{}`{}\nhelp: implement `{}<{}>` for `{}`, or write the operation out",
                           opName(a.expr(id).op), typeMangleName(lt.kind, lt.structName), typeMangleName(rt.kind, rt.structName), hint,
                           trait, typeMangleName(rt.kind, rt.structName), typeMangleName(lt.kind, lt.structName)));
        }
        e: Expr = a.expr(id);
        c: long = self.eqCall(a, fn, e.left, e.right);
        ret: VarType = self.returnOf(fn);
        a.setExpr(id, Expr { op: Op.MethodCall, left: NO_NODE, right: NO_NODE, kind: ret.kind,
                             structName: ret.structName, isParen: e.isParen,
                             payload: Payload.Call(c) });
        return ret;
    }

    // The method a type implements an operator trait with, at another type. A parameterized
    // trait's methods carry the instantiation in their names (which is what lets one type
    // implement `Add` at several) so the right-hand type names the method rather than being
    // searched for. `eqMethodOf` is this at `Eq`/`eq`, kept separate because it is the one that
    // may fall back on a derived implementation.
    opMethodOf &self owner:Sym rhs:VarType trait:str method:str -> Sym {
        if (owner == NO_SYM) { return NO_SYM; }
        inst: Sym = internString(format("{}_{}", trait, typeMangleName(rhs.kind, rhs.structName)));
        cand: Sym = methodSymbol(methodSymbol(owner, inst), intern(method));
        if (self.fnNames.has(nameOf(cand))) { return self.resolveFn(cand); }
        return NO_SYM;
    }

    // What a comparison's left operand implements `Eq` under. A scalar carries implementations
    // too, which in practice means `str`, the one implementable type that is an aggregate and so
    // reaches this path at all; an `int` never does, since the hardware compares it.
    eqOwner &self t:VarType -> Sym {
        if (t.kind == Lit.Struct && t.structName != NO_SYM) { return t.structName; }
        if (isImplableScalar(t.kind)) { return intern(typeName(t.kind)); }
        return NO_SYM;
    }

    // The `eq` a type implements at another type. A parameterized trait's methods carry the
    // instantiation in their names (which is what lets one type be `Eq` at several) so the
    // right-hand type names the method rather than being searched for.
    eqMethodOf &self owner:Sym rhs:VarType -> Sym {
        if (owner == NO_SYM) { return NO_SYM; }
        inst: Sym = internString(format("Eq_{}", typeMangleName(rhs.kind, rhs.structName)));
        cand: Sym = methodSymbol(methodSymbol(owner, inst), intern("eq"));
        if (self.fnNames.has(nameOf(cand))) { return self.resolveFn(cand); }
        return NO_SYM;
    }

    eqCall &self inout a:Ast fn:Sym recv:NodeId arg:NodeId -> long {
        args: Vec<NodeId>;
        args.push(arg);
        a.calls.push(CallNode { name: fn, receiver: recv, firstArg: a.addArgs(args),
                                argCount: 1, slot: NO_SLOT, callee: NO_NODE, sigKey: NO_SYM });
        return a.calls.len() - 1;
    }

    // `<var>.<field>`, with the receiver typed as the parameter holding it is declared.
    eqField &self inout a:Ast v:Sym k:Lit s:Sym f:FieldDef -> NodeId {
        base: NodeId = a.leafOf(Op.Lvalue, Payload.Name(v), k, s);
        a.fields.push(FieldNode { base: base, name: f.name });
        return a.leafOf(Op.FieldAccess, Payload.Field(a.fields.len() - 1), f.kind, f.structName);
    }

    // Can `s` be compared field by field? Answered before anything is generated, so a type whose
    // field is undecidable is refused under its own name rather than reporting the field's type
    // from inside a method the program never wrote.
    //
    // Terminates: a struct cannot contain itself by value, and a pointer field stops the walk
    // rather than following it.
    canDeriveEq &self s:Sym depth:long -> bool {
        if (depth > 32 || s == NO_SYM) { return false; }
        at: long = gReg.findStructSym(s);
        if (at < 0) { return false; }
        d: StructDef = gReg.structDef(at);
        // A tagged union compares by tag and payload, which is not this shape; a struct with no
        // fields has nothing to compare, and can say what it means by hand.
        if (d.isEnum || d.fieldCount == 0) { return false; }
        for k in 0..d.fieldCount {
            f: FieldDef = gReg.fieldAt(d, k);
            // Comparing N elements is a loop, not an expression.
            if (f.isArray) { return false; }
            // A raw pointer compares as an address, which for anything that owns what it points
            // at is the wrong answer and a silent one: two vectors holding equal elements would
            // report unequal because their buffers sit at different places. A type for which
            // identity really is equality can say so by hand.
            if (f.kind == Lit.Ptr) { return false; }
            if (isAggregate(f.kind)) {
                if (f.kind != Lit.Struct) { return false; }        // str / slice / trait object
                // A backed enum is carried as `Lit.Struct` companioned with its own name, but it IS
                // its backing integer: comparing two is an integer compare, and there is no struct
                // row to recurse into. Asking `findStruct` about one would end the walk and refuse
                // the whole type, as it would for `TypeRef { base: Lit, name: Sym }`.
                if (!namedScalar(f.kind, f.structName)) {
                    if (self.eqMethodOf(f.structName, varType(Lit.Struct, f.structName)) == NO_SYM
                        && !self.canDeriveEq(f.structName, depth + 1)) { return false; }
                }
            }
        }
        return true;
    }

    // Derive `S == S` field by field, on demand: only for a type something actually compares.
    // Deriving for every comparable struct would cost assembly in programs that never write `==`:
    // a derived method is registered as a trait implementation, and the pruner roots every one of
    // those because their vtables are `.data` tables it cannot trace.
    //
    // The body is built already resolved and already typed. It has to be: it is generated while
    // the walk that would have typed it is somewhere else in the page, and re-entering that walk
    // here would type a body in the middle of typing another.
    deriveEq &self inout a:Ast s:Sym -> bool {
        if (!self.canDeriveEq(s, 0)) { return false; }
        name: Sym = methodSymbol(methodSymbol(s, internString(format("Eq_{}", nameOf(s)))),
                                 intern("eq"));
        if (self.fnNames.has(nameOf(name))) { return true; }
        d: StructDef = gReg.structDef(gReg.findStructSym(s));
        // Recorded before the body is built, so a field of this same type asks once.
        self.noteReturn(name, varType(Lit.Bool, NO_SYM));

        selfName: Sym = intern("self");
        otherName: Sym = intern("other");
        acc: NodeId = NO_NODE;
        for k in 0..d.fieldCount {
            f: FieldDef = gReg.fieldAt(d, k);
            lhs: NodeId = self.eqField(a, selfName, Lit.Ref, s, f);
            rhs: NodeId = self.eqField(a, otherName, Lit.Struct, s, f);
            one: NodeId = NO_NODE;
            if (f.kind == Lit.Struct && !namedScalar(f.kind, f.structName)) {
                // A struct field answers for itself: with its own implementation when it has
                // one, and otherwise with a derivation of its own made here, which is what makes
                // the derive reach all the way down. A backed-enum field is not one of these: it
                // takes the integer compare below, the same one a bare `Tok` or `Lit` gets.
                fe: Sym = self.eqMethodOf(f.structName, varType(Lit.Struct, f.structName));
                if (fe == NO_SYM && self.deriveEq(a, f.structName)) {
                    fe = self.eqMethodOf(f.structName, varType(Lit.Struct, f.structName));
                }
                one = a.leafOf(Op.MethodCall, Payload.Call(self.eqCall(a, fe, lhs, rhs)),
                               Lit.Bool, NO_SYM);
            } else {
                one = a.binary(Op.IsEqual, lhs, rhs, Lit.Int);
            }
            if (acc == NO_NODE) { acc = one; }
            else { acc = a.binary(Op.LogicalAnd, acc, one, Lit.Int); }
        }

        params: Vec<long>;
        a.decls.push(VarDeclNode { name: selfName, kind: Lit.Ref, structName: s, isArray: false,
                                   count: 0, conv: Conv.None, isVariadic: false,
                                   elemKind: Lit.Void, elemStruct: NO_SYM, init: NO_NODE });
        params.push(a.decls.len() - 1);
        a.decls.push(VarDeclNode { name: otherName, kind: Lit.Struct, structName: s,
                                   isArray: false, count: 0, conv: Conv.None, isVariadic: false,
                                   elemKind: Lit.Void, elemStruct: NO_SYM, init: NO_NODE });
        params.push(a.decls.len() - 1);
        a.returns.push(ReturnNode { value: acc });
        body: Vec<long>;
        body.push(a.addStmt(StmtKind.Return, a.returns.len() - 1));
        firstArg: long = a.params.len();
        a.params.extend(params);
        a.fns.push(FnNode { name: name, returnKind: Lit.Bool, returnStruct: NO_SYM,
                            visibility: Vis.Pub, file: NO_SYM, pkg: NO_SYM,
                            isUnsafe: false, isTemplate: false, inferReturn: false,
                            firstBound: 0, boundCount: 0, firstArg: firstArg,
                            argCount: params.len(), body: a.addBlock(body) });
        self.fnAt.put(nameOf(name), a.fns.len() - 1);
        self.eqExtra.push(a.addStmt(StmtKind.FunctionDef, a.fns.len() - 1));

        args: Vec<TypeRef>;
        args.push(TypeRef { base: Lit.Struct, name: s });
        fns: Vec<Sym>;
        fns.push(name);
        gReg.addImpl(s, TraitRef { name: intern("Eq"), firstArg: gReg.addTraitArgs(args),
                                   argCount: 1 }, fns);
        return true;
    }

    // ─── nameof ──────────────────────────────────────────────────────────────

    // `nameof(E, v)`: the name of the variant `v` holds. The node carries the enum in
    // `structName` and the value in its payload; it becomes an ordinary call to a derived
    // `E_nameof`, after which nothing downstream knows the builtin existed.
    checkNameOf &self inout a:Ast id:NodeId -> VarType {
        e: Expr = a.expr(id);
        val: NodeId = NO_NODE;
        p: Payload = e.payload;
        match p { Sub(v) { val = v; } _ { } }
        self.checkExpr(a, val);

        fn: Sym = self.deriveNameOf(a, e.structName);
        args: Vec<NodeId>;
        args.push(val);
        a.calls.push(CallNode { name: fn, receiver: NO_NODE, firstArg: a.addArgs(args),
                                argCount: 1, slot: NO_SLOT, callee: NO_NODE, sigKey: NO_SYM });
        a.setExpr(id, Expr { op: Op.FunctionCall, left: NO_NODE, right: NO_NODE, kind: Lit.Str,
                             structName: NO_SYM, isParen: e.isParen,
                             payload: Payload.Call(a.calls.len() - 1) });
        return varType(Lit.Str, NO_SYM);
    }

    // `E_nameof v -> str`: the name of the variant `v` holds, derived from the enum's declaration
    // the first time `nameof(E, ...)` is met. It is an if-chain over the variants' values that
    // returns string literals: the name table a program would otherwise keep by hand, kept by the
    // compiler instead. A backed enum's value is its backing integer and arrives as one; a sum
    // type arrives as a borrow, whose `$tag` field is the discriminant.
    //
    // Built already resolved and already typed, for the reason a derived `eq` is: it is generated
    // while the walk that would have typed it is somewhere else in the page.
    deriveNameOf &self inout a:Ast en:Sym -> Sym {
        name: Sym = internString(format("{}_nameof", nameOf(en)));
        if (self.fnNames.has(nameOf(name))) { return name; }
        at: long = gReg.findEnumSym(en);
        if (at < 0) { return name; }
        ed: EnumDef = gReg.enumDef(at);
        // Recorded before the body is built, so a caller reads `str` whichever order they are met.
        self.noteReturn(name, varType(Lit.Str, NO_SYM));

        vn: Sym = intern("v");
        pKind: Lit = ed.backing;
        pStruct: Sym = NO_SYM;
        if (ed.hasPayload) { pKind = Lit.Ref; pStruct = en; }

        body: Vec<long>;
        for k in 0..ed.variantCount {
            vd: VariantDef = gReg.variantAt(ed, k);
            tag: NodeId = a.leafOf(Op.Lvalue, Payload.Name(vn), pKind, pStruct);
            if (ed.hasPayload) {
                a.fields.push(FieldNode { base: tag, name: intern(enumTagField()) });
                tag = a.leafOf(Op.FieldAccess, Payload.Field(a.fields.len() - 1),
                               ed.backing, NO_SYM);
            }
            test: NodeId = a.binary(Op.IsEqual, tag,
                                    a.leaf(Op.Literal, Payload.Num(vd.value), ed.backing),
                                    Lit.Int);
            a.returns.push(ReturnNode { value: a.leafOf(Op.StringLit, Payload.Text(vd.name),
                                                        Lit.Str, NO_SYM) });
            arm: Vec<long>;
            arm.push(a.addStmt(StmtKind.Return, a.returns.len() - 1));
            a.ifs.push(IfNode { cond: test, body: a.addBlock(arm), elseIf: -1 });
            body.push(a.addStmt(StmtKind.If, a.ifs.len() - 1));
        }
        // Unreachable for a value the type system produced; a corrupted one names itself.
        a.returns.push(ReturnNode { value: a.leafOf(Op.StringLit, Payload.Text(intern("?")),
                                                    Lit.Str, NO_SYM) });
        body.push(a.addStmt(StmtKind.Return, a.returns.len() - 1));

        a.decls.push(VarDeclNode { name: vn, kind: pKind, structName: pStruct,
                                   isArray: false, count: 0, conv: Conv.None, isVariadic: false,
                                   elemKind: Lit.Void, elemStruct: NO_SYM, init: NO_NODE });
        params: Vec<long>;
        params.push(a.decls.len() - 1);
        firstArg: long = a.params.len();
        a.params.extend(params);
        a.fns.push(FnNode { name: name, returnKind: Lit.Str, returnStruct: NO_SYM,
                            visibility: Vis.Pub, file: NO_SYM, pkg: NO_SYM,
                            isUnsafe: false, isTemplate: false, inferReturn: false,
                            firstBound: 0, boundCount: 0, firstArg: firstArg,
                            argCount: 1, body: a.addBlock(body) });
        self.fnAt.put(nameOf(name), a.fns.len() - 1);
        self.eqExtra.push(a.addStmt(StmtKind.FunctionDef, a.fns.len() - 1));
        return name;
    }

    // A call yields what the function returns. A method call is rewritten here into an ordinary
    // call to `T_method`, with the receiver as the first argument: after which nothing downstream
    // has to know methods exist.
    checkCall &self inout a:Ast id:NodeId c:long -> VarType {
        mark: long = self.scalarLends.len();
        t: VarType = self.checkCallHere(a, id, c);
        // A call through a value or a dispatch has no declaration to make `&n` a lend.
        if (self.scalarLends.len() > mark) {
            while (self.scalarLends.len() > mark) { self.scalarLends.pop(); }
            self.requireUnsafe("taking a raw address with `&`");
        }
        return t;
    }

    checkCallHere &self inout a:Ast id:NodeId c:long -> VarType {
        cn: CallNode = a.calls.get(c);
        // The type this call's result is stored into, if the caller said; cleared before the
        // arguments are checked so a call nested in one of them does not read it.
        want: Sym = self.expectType;
        self.expectType = NO_SYM;
        if (cn.receiver != NO_NODE && nameOf(cn.name) == SPLICE_METHOD) { return self.checkSplice(a, id, c, cn); }
        // `Show.text(x)`: the trait's method for x's type, named when two traits give the type a
        // method of one name. The first argument is the receiver from here on, and the call is
        // the method call `x.text()` held to that trait.
        forced: Sym = self.traitNamed(a, cn.receiver);
        // `Fresh.new()`: a trait's static method (no receiver), for the type the call's
        // destination says (`p: P = Fresh.new();`), as a generic type's static call reads its
        // instance there. The receiver becomes that type, and the static path below takes the
        // trait's implementation rather than asking which.
        forcedStatic: bool = false;
        if (forced != NO_SYM && self.traitMethodIsStatic(forced, cn.name)) {
            if (want == NO_SYM) {
                failStr(format("cannot infer which type `{}.{}(...)` is called for\nnote: `{}` is a static method of `{}`, called for the type its result is stored into, and nothing here says which type that is\nhelp: write `x: T = {}.{}(...)`",
                               lastComponentOf(nameOf(forced)), nameOf(cn.name), nameOf(cn.name), lastComponentOf(nameOf(forced)),
                               lastComponentOf(nameOf(forced)), nameOf(cn.name)));
            }
            forcedStatic = true;
            cn = CallNode { name: cn.name, receiver: a.leafOf(Op.Lvalue, Payload.Name(want), Lit.Struct, want),
                            firstArg: cn.firstArg, argCount: cn.argCount, slot: NO_SLOT, callee: NO_NODE,
                            sigKey: NO_SYM };
            a.calls.set(c, cn);
        } else if (forced != NO_SYM) {
            if (cn.argCount == 0) {
                failStr(format("too few arguments to `{}.{}`: expected at least 1, found 0\nnote: `{}.{}(x)` calls the trait's method on the value it is handed first",
                               lastComponentOf(nameOf(forced)), nameOf(cn.name),
                               lastComponentOf(nameOf(forced)), nameOf(cn.name)));
            }
            cn = CallNode { name: cn.name, receiver: a.argAt(cn, 0), firstArg: cn.firstArg + 1,
                            argCount: cn.argCount - 1, slot: NO_SLOT, callee: NO_NODE, sigKey: NO_SYM };
            a.calls.set(c, cn);
        }
        recv: VarType = varType(Lit.Void, NO_SYM);
        if (cn.receiver != NO_NODE) { recv = self.checkExpr(a, cn.receiver); }
        // `s.len()` on a type whose length is a field (`str`, a slice, `String`: anything with a
        // `len` field and no `len` method) reads the field, so `len()` is spelled the same on
        // every string and container. The receiver is already typed: the node becomes the field.
        if (cn.receiver != NO_NODE && cn.argCount == 0 && forced == NO_SYM && nameOf(cn.name) == "len") {
            lt: VarType = self.lenField(recv);
            if (lt.kind != Lit.Void) {
                a.fields.push(FieldNode { base: cn.receiver, name: cn.name });
                a.setExpr(id, Expr { op: Op.FieldAccess, left: NO_NODE, right: NO_NODE, kind: lt.kind,
                                     structName: lt.structName, isParen: a.expr(id).isParen,
                                     payload: Payload.Field(a.fields.len() - 1) });
                return lt;
            }
        }

        lendMark: long = self.scalarLends.len();
        // `k.f(x)` where `f` is a field holding a closure rather than a method of `k`: the call
        // goes through what the field holds, which answers `call` like any other. Rewritten
        // before the arguments are read, because an argument may be another such call and a
        // rewritten one must not be met a second time: by then its name is already resolved.
        if (recv.structName != NO_SYM) {
            cf: long = self.callableField(recv.structName, cn.name);
            if (cf >= 0) {
                cd: StructDef = gReg.structDef(gReg.findStructSym(recv.structName));
                cfd: FieldDef = gReg.fieldAt(cd, cf);
                a.fields.push(FieldNode { base: cn.receiver, name: cn.name });
                cn = CallNode { name: intern("call"),
                                receiver: a.leafOf(Op.FieldAccess,
                                                   Payload.Field(a.fields.len() - 1),
                                                   cfd.kind, cfd.structName),
                                firstArg: cn.firstArg, argCount: cn.argCount,
                                slot: NO_SLOT, callee: NO_NODE, sigKey: NO_SYM };
                a.calls.set(c, cn);
                recv = varType(cfd.kind, cfd.structName);
            }
        }

        // A generic call (or a macro call) standing as an argument takes the parameter's declared
        // type as its destination, as one stored into a declared variable does: in
        // `m.getOr(fixedOf("k"), 0)` it is getOr's `K` that says what `fixedOf`'s N is. The
        // parameter is read off the callee before the arguments are typed, which is possible
        // exactly when the callee is not itself generic (a generic one is inferred FROM them).
        // Asked once, and only when an argument is a call at all: most are names and literals.
        aimAt: long = -2;
        for k in 0..cn.argCount {
            arg: NodeId = a.argAt(cn, k);
            want: Sym = NO_SYM;
            // `&arr` of an array local or field, handed to an `inout [T]` parameter: the lend of
            // its elements, `&arr[..]`, as a struct local's `&s` is the lend of the struct.
            if (self.unsafeDepth == 0 && self.arrayLendArg(a, arg)) {
                if (aimAt == -2) { aimAt = self.calleeForArgs(a, cn, recv); }
                if (aimAt >= 0) { self.decayArrayLend(a, aimAt, cn, k, arg); }
            }
            ae: Expr = a.expr(arg);
            if ((ae.op == Op.MacroCall || ae.op == Op.FunctionCall || ae.op == Op.MethodCall || ae.op == Op.StructLit
                 || ae.op == Op.TupleLit) && self.wantsDestination(a, arg)) {
                if (aimAt == -2) { aimAt = self.calleeForArgs(a, cn, recv); }
                if (aimAt >= 0) { want = self.paramWant(a, aimAt, cn, k); }
            }
            wasLending: NodeId = self.lendingArg;
            if (ae.op == Op.AddressOf) { self.lendingArg = arg; }
            if (want != NO_SYM) { self.checkAimed(a, arg, want); } else { self.checkExpr(a, arg); }
            self.lendingArg = wasLending;
        }

        // `File.open(path)`: the receiver is a type, not a value, so this is a static method:
        // an ordinary call to `File_open` with no `self` in front of the arguments.
        st: Sym = self.staticOwner(a, cn.receiver);
        if (st != NO_SYM) {
            fn: Sym = self.resolveFn(methodSymbol(st, cn.name));
            // `Point.zero()` where `zero` is a trait this module owns: as for an instance method.
            mine: Sym = NO_SYM;
            if (forcedStatic) {
                // `Fresh.new()`: that trait's implementation (a core trait's keeps the plain name).
                mine = self.traitMethodFor(a, st, forced, cn);
            } else { mine = self.ownTraitMethod(a, st, cn.name, cn); }
            if (mine != NO_SYM) { fn = mine; }
            else if (forcedStatic) { }
            // A static method a carried implementation gives (`R.new()` from a trait whose `new`
            // carries its name beside core `Default`'s), or one of two of them: as for a method.
            else if (!gReg.carriedOwners.isEmpty() && !gReg.isGenericSym(st)) {
                fn = self.carriedAmbiguity(a, c, st, cn.name, fn, true);
            }
            // A static method of a parameterized trait's implementation carries the trait's
            // instantiation (`Result_Try_T_E_fromResidual`): found as a method call's is
            // (`overload`).
            if (self.fnNodeOf(fn) < 0 && !self.fnNames.has(nameOf(fn))) {
                ov: Sym = self.staticOverload(a, st, cn);
                if (ov != NO_SYM) { fn = ov; }
            }
            // `Option.fromFlag(true, 5)`: a static method of a generic type, named by the
            // template. Which instance is meant is read off the arguments and the destination.
            if (gReg.isGenericSym(st)) { fn = self.instantiateOwner(a, cn, st, fn, want); }
            // `T.decode(inp)` on a type with no `decode`: a trait's static method, derived or
            // stamped for it now, exactly as an instance method is below.
            else if (!self.fnNames.has(nameOf(fn)) && self.implementForMethod(a, st, cn.name, true)) {
                fn = self.resolveFn(methodSymbol(st, cn.name));
                derived: Sym = self.ownTraitMethod(a, st, cn.name, cn);
                if (derived != NO_SYM) { fn = derived; }
            }
            // `L.bind(addr)`: a static method with type parameters of its own.
            fn = self.instantiate(a, cn, fn, want, 0);
            // `String.from(..)` where String has no `from`: said here, at the call, rather than
            // by the emitter as a call to a function nobody defined.
            if (self.fnNodeOf(fn) < 0 && !self.fnNames.has(nameOf(fn))) {
                // `Ret.fromResidual($tryN.residual())`, a `?`'s early return: the return type is
                // what has no `Try`.
                if (cn.argCount == 1 && self.readsTryLocal(a, a.argAt(cn, 0))) {
                    failStr(format("cannot use `?` in a function that returns `{}`\nnote: `?` returns early with the failure, so the function must return a type implementing `Try`, such as a `Result` or an `Option`",
                                   self.spellType(self.currentReturn.kind, self.currentReturn.structName)));
                }
                failStr(format("no static method `{}` on type `{}`", nameOf(cn.name), self.spellType(Lit.Struct, st)));
            }
            self.requireSafeCallee(a, fn);
            self.boxTraitArgsStatic(a, cn, fn);
            self.holdScalarLends(a, cn, fn, fn, 0, lendMark);
            self.dropReadLends(a, cn, fn, 0);
            self.checkFnArgs(a, cn, fn, 0);
            a.calls.set(c, CallNode { name: fn, receiver: NO_NODE,
                                      firstArg: cn.firstArg, argCount: cn.argCount,
                                      slot: NO_SLOT, callee: NO_NODE, sigKey: NO_SYM });
            return self.returnOf(fn);
        }

        target: Sym = cn.name;
        slot: long = NO_SLOT;
        // A call whose name is a fn-typed variable calls through the value it holds. Checked
        // before resolution, because there is no function of that name to resolve to.
        if (cn.receiver == NO_NODE) {
            held: VarType = self.lookup(cn.name);
            if (held.kind == Lit.Fn) {
                want: long = fnSigArity(held.structName);
                if (want >= 0 && cn.argCount != want) {
                    failStr(format("wrong number of arguments in the call through `{}`: expected {}, found {}",
                                   nameOf(cn.name), want, cn.argCount));
                }
                // Under the name the variable resolves to. A file global's is its qualified one,
                // which is what the lowerer's `isGlobalName` answers for; the bare spelling would
                // read a local slot of that name, which nothing wrote.
                a.calls.set(c, CallNode { name: self.resolveVar(cn.name), receiver: cn.receiver,
                                          firstArg: cn.firstArg, argCount: cn.argCount,
                                          slot: SLOT_FNPTR, callee: NO_NODE,
                                          sigKey: held.structName });
                return fnSigReturn(held.structName);
            }
            // A closure, or a variable typed by an `Fn` bound or held as an `Fn` trait object:
            // `f(x)` is `f.call(x)`, which is where the body actually lives. Rewritten into a
            // method call and left to the code below, so a bound and a trait object take the
            // same two paths every other method call does.
            if (self.callable(held)) {
                cn = CallNode { name: intern("call"),
                                receiver: a.leafOf(Op.Lvalue, Payload.Name(cn.name),
                                                   held.kind, held.structName),
                                firstArg: cn.firstArg, argCount: cn.argCount,
                                slot: NO_SLOT, callee: NO_NODE, sigKey: NO_SYM };
                a.calls.set(c, cn);
                recv = held;
            }
        }
        if (cn.receiver != NO_NODE) {
            owner: Sym = recv.structName;
            // A scalar can carry methods too: `methods long for Hash`. It has no companion name,
            // so the type's own spelling is what the method was declared under.
            if (owner == NO_SYM && recv.kind != Lit.Void) { owner = intern(typeName(recv.kind)); }
            if (owner == NO_SYM) { return varType(Lit.Void, NO_SYM); }
            // A trait object does not know which function it will reach: it carries a vtable,
            // and the method's position in the trait is the slot to load from it. Everything
            // else resolves statically to `T_method`.
            if (recv.kind == Lit.TraitObj) {
                if (forced != NO_SYM && forced != owner) {
                    failStr(format("cannot call `{}.{}(...)` on a trait object of `{}`\nnote: an object of `{}` has the methods of `{}` and no others",
                                   lastComponentOf(nameOf(forced)), nameOf(cn.name), self.spellType(Lit.TraitObj, owner),
                                   self.spellType(Lit.TraitObj, owner), self.spellType(Lit.TraitObj, owner)));
                }
                return self.checkDispatch(a, c, cn, owner);
            }
            // `t.apply(v)` where `apply` is a fn-typed field, not a method: the call goes through
            // whatever the field holds. A field has no name to look up, so the callee travels as
            // the field-access expression itself.
            fld: long = self.fnField(owner, cn.name);
            if (fld >= 0) {
                d: StructDef = gReg.structDef(gReg.findStructSym(owner));
                f: FieldDef = gReg.fieldAt(d, fld);
                a.fields.push(FieldNode { base: cn.receiver, name: cn.name });
                fe: NodeId = a.leafOf(Op.FieldAccess, Payload.Field(a.fields.len() - 1),
                                      Lit.Fn, f.structName);
                // The field's signature is what this call is held to: it is checked here rather
                // than left to arrive at whatever the field happens to hold with the wrong stack.
                want: long = fnSigArity(f.structName);
                if (want >= 0 && cn.argCount != want) {
                    failStr(format("wrong number of arguments in the call through `{}.{}`: expected {}, found {}",
                                   nameOf(owner), nameOf(cn.name), want, cn.argCount));
                }
                a.calls.set(c, CallNode { name: cn.name, receiver: NO_NODE,
                                          firstArg: cn.firstArg, argCount: cn.argCount,
                                          slot: SLOT_FNPTR, callee: fe,
                                          sigKey: f.structName });
                return fnSigReturn(f.structName);
            }
            target = methodSymbol(owner, cn.name);
            // A trait this module owns is asked first, as every name is looked up here before
            // anywhere else: `x.cmp(y)` on a `long` in a file with its own `trait Ord` is that
            // trait's, though the standard library's `long_cmp` exists too.
            mine: Sym = self.ownTraitMethod(a, owner, cn.name, cn);
            if (mine != NO_SYM) { target = mine; }
            // Named by its trait (`Show.text(x)`), or one of two traits' methods of one name.
            if (forced != NO_SYM) {
                pick: Sym = self.traitMethodFor(a, owner, forced, cn);
                if (pick != NO_SYM) { target = pick; }
            } else if (!gReg.carriedOwners.isEmpty()) {
                target = self.carriedAmbiguity(a, c, owner, cn.name, target, false);
            }
            // No plain method of that name: it may be one a parameterized trait contributes,
            // whose name carries the instantiation because several of them can coexist.
            if (!self.fnNames.has(nameOf(target))) {
                first: NodeId = NO_NODE;
                if (cn.argCount > 0) { first = a.argAt(cn, 0); }
                over: Sym = self.overload(a, owner, cn.name, first);
                if (over != NO_SYM) { target = over; }
                // A trait declaring the method may still be implemented: a generic type's
                // conditional implementation whose bounds a derive since met, or the trait's
                // own derive. Either registers `owner_m`, typed by the trait's signature.
                else if (recv.kind != Lit.TraitObj && self.implementForMethod(a, owner, cn.name, false)) {
                    // A derive of this module's own trait names its methods after the trait.
                    derived: Sym = self.ownTraitMethod(a, owner, cn.name, cn);
                    if (derived != NO_SYM) { target = derived; }
                }
                // `x.clone()` on a struct that never wrote one: `Clone` is derived, field by
                // field, and this is what asks for it.
                //
                // What it will return has to be known now, not when the derived body is checked
                // next round: the derivation happens after this expression is typed, and a call
                // left typed `void` gets no destination slot, so the caller would read a struct
                // out of a return register that never held one. A derived `clone` returns Self,
                // which is exactly the receiver's type, so there is nothing to wait for.
                //
                // Only where deriving one is sound (`cloneBlocker`): a type with a `drop` of its
                // own, or one holding an owning field that has no clone, would come out sharing
                // what it owns with the original, both released. A generic type's own `clone`
                // whose bound this instance misses says that instead.
                else if (nameOf(cn.name) == "clone" && recv.kind != Lit.TraitObj
                         && gReg.hasStructSym(owner)) {
                    why: str = gReg.cloneBlocker(owner);
                    if (why.len == 0 && !gReg.cloneByTemplate(owner)) {
                        self.wantedClones.push(owner);
                        self.noteReturn(target, varType(Lit.Struct, owner));
                    } else if (!self.templateMethodPending(a, owner, cn.name)) {
                        if (why.len == 0) { why = "its generic type's own `clone` was not stamped for it"; }
                        failStr(format("`{}` does not implement `Clone`\nnote: {}\nhelp: write `methods {} for Clone`, or move the value instead",
                                       self.spellType(Lit.Struct, owner), why,
                                       self.spellType(Lit.Struct, owner)));
                    }
                }
                // A plain value's clone is the value: `x.clone()` on a `long`, a `str`, a pointer
                // or a backed enum is `x`. What lets a `T: Clone` body run for a scalar `T`.
                else if (nameOf(cn.name) == "clone" && cn.argCount == 0
                         && self.plainClone(recv)) {
                    rv: Expr = a.expr(cn.receiver);
                    a.setExpr(id, rv);
                    return varType(rv.kind, rv.structName);
                }
                else { self.refuseNoMethod(a, owner, cn.name, self.readsTryLocal(a, cn.receiver)); }
            }
        }
        // `assert!`'s failure: the program's `@panic` function, found by that attribute.
        if (cn.receiver == NO_NODE && nameOf(target) == "$panic") {
            target = self.panicTarget(a);
            if (target == NO_SYM) {
                failStr(stringOf("`assert!` needs a `@panic` function, and nothing is marked `@panic`\nnote: a failed `assert!` calls the program's `@panic` function\nhelp: `#include <stdlib::panic>`, or declare one: `@panic name msg:str -> never { ... }`"));
            }
        }
        resolved: Sym = self.resolveFn(target);
        preInst: Sym = resolved;
        // A plain call to a name no function has: refused here, where it is written, rather than
        // reported by the emitter as a call to a function nobody defined.
        if (cn.receiver == NO_NODE && self.fnNodeOf(resolved) < 0 && !self.fnNames.has(nameOf(resolved))) {
            failStr(format("cannot find function `{}` in this scope", nameOf(cn.name)));
        }
        if (cn.receiver == NO_NODE) { resolved = self.instantiate(a, cn, resolved, want, 0); }
        // A method with type parameters of its own, called on a value: stamped per call, as a
        // generic function is, from the arguments after the receiver and from the destination.
        else { resolved = self.instantiate(a, cn, resolved, want, 1); }
        self.requireVisible(a, resolved);
        if (!self.withHolds.has(c)) { self.requireSafeCallee(a, resolved); }
        self.boxTraitArgs(a, cn, resolved);
        rbase: long = 0;
        if (cn.receiver != NO_NODE) { rbase = 1; }
        self.holdScalarLends(a, cn, resolved, preInst, rbase, lendMark);
        self.dropReadLends(a, cn, resolved, rbase);
        self.checkFnArgs(a, cn, resolved, rbase);
        // Written back, so lowering emits a call to the name that was actually declared.
        a.calls.set(c, CallNode { name: resolved, receiver: cn.receiver,
                                  firstArg: cn.firstArg, argCount: cn.argCount, slot: slot,
                                  callee: NO_NODE, sigKey: NO_SYM });
        return self.returnOf(resolved);
    }

    // The type of `len` read as a field, when `x.len()` means it: a `str` or a slice, or a struct
    // with a `len` field and no `len` method of its own. Void otherwise.
    lenField &self t:VarType -> VarType {
        none: VarType = varType(Lit.Void, NO_SYM);
        if (t.isArray) { return none; }
        if (t.kind == Lit.Str || t.kind == Lit.Slice) { return varType(Lit.Long, NO_SYM); }
        if ((t.kind != Lit.Struct && t.kind != Lit.Ref) || t.structName == NO_SYM) { return none; }
        if (self.fnNames.has(nameOf(methodSymbol(t.structName, intern("len"))))) { return none; }
        sd: long = gReg.findStructSym(t.structName);
        if (sd < 0) { return none; }
        d: StructDef = gReg.structDef(sd);
        k: long = gReg.findField(d, "len");
        if (k < 0) { return none; }
        fd: FieldDef = gReg.fieldAt(d, k);
        if (fd.isArray || isAggregate(fd.kind)) { return none; }
        return varType(fd.kind, fd.structName);
    }

    // `x.m()` where x's type has no method `m` and none can arrive (no overload, no trait to derive
    // it from, not `clone`). It is refused here, at the call, where it can be said why; otherwise
    // the call would survive to the emitter as a call to a function nobody defined, reported with
    // no position. There are two answers: a generic type's method declared in a block whose bound
    // this instance does not meet (`extendSlice` in `methods Vec<T: Copy>`, on a `Vec<String>`),
    // and a method that does not exist at all. It stays silent where the type is not settled yet
    // (an instance not laid out, or a method of one whose bounds hold but which is not stamped
    // yet): those are another round's to decide. `tryOp` says the receiver is a `?`'s operand
    // (`readsTryLocal`) and the method one of `Try`'s, so it is the `?` that is refused.
    refuseNoMethod &self inout a:Ast owner:Sym m:Sym tryOp:bool -> void {
        on: str = nameOf(owner);
        if (gReg.findStruct(on) < 0 && gReg.findEnum(on) < 0 && !namesScalar(on)) { return; }
        if (self.templateMethodPending(a, owner, m)) { return; }
        if (tryOp) { self.refuseTryOperand(varType(Lit.Struct, owner)); }
        why: str = "";
        sd: long = gReg.findStruct(on);
        if (sd >= 0 && gReg.findFieldSym(gReg.structDef(sd), m) >= 0) {
            why = keepString(format("\nnote: `{}` is a field\nhelp: read it without `()`", nameOf(m)));
        }
        failStr(format("no method `{}` on type `{}`{}", nameOf(m), self.spellType(Lit.Struct, owner), why));
    }

    // `owner` is an instance of a generic type whose template declares `m` in a block with
    // bounds: refused here when this instance misses one; true when every bound holds (it is
    // stamped in a later round); false when the template declares no such method.
    templateMethodPending &self inout a:Ast owner:Sym m:Sym -> bool {
        on: str = nameOf(owner);
        ti: long = NOT_FOUND;
        r: long = gReg.findRequest(on);
        if (r >= 0) { ti = gReg.findTemplateSym(gReg.requestAt(r).base); }
        if (ti >= 0) {
            t: GTemplate = gReg.templateDef(ti);
            gm: Sym = methodSymbol(t.name, m);
            for k in 0..a.fns.len() {
                f: FnNode = a.fns.get(k);
                if (f.isTemplate && f.name == gm) {
                    req: GRequest = gReg.requestAt(r);
                    for b in 0..f.boundCount {
                        mb: MethodBound = gReg.boundAt(f.firstBound + b);
                        if (mb.param < req.argCount) {
                            arg: TypeRef = gReg.gArgAt(req, mb.param);
                            if (!self.late.satisfies(arg, mb.trait.name)) {
                                tr: str = lastComponentOf(nameOf(mb.trait.name));
                                failStr(format("no method `{}` on type `{}`\nnote: `{}` is declared for `{}: {}` only, and `{}` does not implement `{}`",
                                               nameOf(m), self.spellType(Lit.Struct, owner), nameOf(m),
                                               nameOf(gReg.gParamAt(t, mb.param)), tr,
                                               self.spellType(arg.base, arg.name), tr));
                            }
                        }
                    }
                    return true;     // every bound holds: it is stamped in a later round
                }
            }
        }
        return false;
    }

    // The function a call will reach, when that is already known before its arguments are typed
    // and it is not a template: a method of the receiver's type, a static method, a plain
    // function. -1 otherwise (a template, a dispatch, a call through a value, an overload the
    // first argument picks). Asks and changes nothing: `checkCall` resolves for real after.
    calleeForArgs &self inout a:Ast cn:CallNode recv:VarType -> long {
        fn: Sym = NO_SYM;
        if (cn.receiver != NO_NODE) {
            st: Sym = self.staticOwner(a, cn.receiver);
            if (st != NO_SYM && self.isTypeTemplate(st)) { return -1; }   // the instance is not known yet
            if (st != NO_SYM) { fn = self.resolveFn(methodSymbol(st, cn.name)); }
            else {
                if (recv.kind == Lit.TraitObj) { return -1; }
                owner: Sym = recv.structName;
                if (owner == NO_SYM && recv.kind != Lit.Void) { owner = intern(typeName(recv.kind)); }
                if (owner == NO_SYM) { return -1; }
                t: Sym = methodSymbol(owner, cn.name);
                if (!self.fnNames.has(nameOf(t))) { return -1; }
                fn = self.resolveFn(t);
            }
        } else {
            if (self.lookup(cn.name).kind != Lit.Void) { return -1; }   // a variable: called through
            fn = self.resolveFn(cn.name);
        }
        at: long = self.fnNodeOf(fn);
        if (at < 0 || a.fns.get(at).isTemplate) { return -1; }
        return at;
    }

    // A call to a generic function, a macro call (which may expand to one), or a variant of a
    // generic enum built without saying which instance (`Option.Some(5)`): what a destination
    // can settle.
    wantsDestination &self inout a:Ast arg:NodeId -> bool {
        e: Expr = a.expr(arg);
        if (e.op == Op.MacroCall || e.op == Op.TupleLit) { return true; }
        if (e.op == Op.StructLit) {
            match e.payload { Lit(l) { return gReg.findTemplateSym(a.lits.get(l).typeName) >= 0; } _ { } }
            return false;
        }
        if (e.op != Op.FunctionCall && e.op != Op.MethodCall) { return false; }
        c: long = -1;
        match e.payload { Call(i) { c = i; } _ { return false; } }
        cn: CallNode = a.calls.get(c);
        // `Fresh.new()`: a trait's static method is for the type its result goes to.
        if (e.op == Op.MethodCall) {
            tr: Sym = self.traitNamed(a, cn.receiver);
            return tr != NO_SYM && self.traitMethodIsStatic(tr, cn.name);
        }
        if (cn.receiver != NO_NODE || cn.callee != NO_NODE) { return false; }
        if (self.lookup(cn.name).kind != Lit.Void) { return false; }
        at: long = self.fnNodeOf(self.resolveFn(cn.name));
        return at >= 0 && a.fns.get(at).isTemplate;
    }

    // `&x` where `x` is a fixed array (a local, a parameter, a field of one).
    arrayLendArg &self inout a:Ast arg:NodeId -> bool {
        e: Expr = a.expr(arg);
        if (e.op != Op.AddressOf) { return false; }
        inner: NodeId = NO_NODE;
        p: Payload = e.payload;
        match p { Sub(v) { inner = v; } _ { return false; } }
        return self.placeIsArray(a, inner).isArray;
    }

    // The declared type of a place made of names and fields (`h.cells`, `self.grid.rows`), read
    // without typing it. The argument is typed once, later; typing it here as well would resolve
    // its calls twice (`&gs.at(0).xs` would then look `at` up under its already-resolved name).
    // A place with anything else in it (a call, an index) answers not-an-array.
    placeIsArray &self inout a:Ast id:NodeId -> VarType {
        none: VarType = varType(Lit.Void, NO_SYM);
        e: Expr = a.expr(id);
        p: Payload = e.payload;
        match p {
            Name(n) { return self.lookup(self.resolveVar(n)); }
            Field(f) {
                fd: FieldNode = a.fields.get(f);
                bt: VarType = self.placeIsArray(a, fd.base);
                if (bt.isArray || (bt.kind != Lit.Struct && bt.kind != Lit.Ref)) { return none; }
                si: long = gReg.findStructSym(bt.structName);
                if (si < 0) { return none; }
                d: StructDef = gReg.structDef(si);
                fi: long = gReg.findFieldSym(d, fd.name);
                if (fi < 0) { return none; }
                fdef: FieldDef = gReg.fieldAt(d, fi);
                return VarType { kind: fdef.kind, structName: fdef.structName, isArray: fdef.isArray };
            }
            _ { }
        }
        return none;
    }

    // The lend of an array to parameter `k` of the callee at `at`: a slice parameter takes its
    // elements (`&arr` is written `&arr[..]`); anything else is refused with what to write, since a
    // type parameter cannot stand for an array and `swapValues(&a, &b)` would swap two slices.
    decayArrayLend &self inout a:Ast at:long cn:CallNode k:long arg:NodeId -> void {
        f: FnNode = a.fns.get(at);
        i: long = k;
        if (cn.receiver != NO_NODE && self.staticOwner(a, cn.receiver) == NO_SYM) { i = k + 1; }
        if (i >= f.argCount) { return; }
        p: VarDeclNode = a.paramAt(f, i);
        e: Expr = a.expr(arg);
        inner: NodeId = NO_NODE;
        ep: Payload = e.payload;
        match ep { Sub(v) { inner = v; } _ { return; } }
        if (p.kind == Lit.Slice && !p.isVariadic) {
            a.indexes.push(IndexNode { name: NO_SYM, base: inner, index: NO_NODE, whole: true,
                                       rawPointerBase: false, sliceStart: NO_NODE,
                                       sliceEnd: NO_NODE, at: NO_SYM });
            whole: NodeId = a.leaf(Op.ArrayIndex, Payload.Index(a.indexes.len() - 1), Lit.Int);
            e.payload = Payload.Sub(whole);
            a.setExpr(arg, e);
            return;
        }
        failStr(format("cannot lend a whole array to parameter `{}`\nnote: a type parameter or a struct cannot stand for an array\nhelp: lend its elements as a slice (`&xs[..]` to an `inout [T]` parameter), or wrap the array in a struct",
                       nameOf(p.name)));
    }

    // The type argument `k` of call `cn` is handed to, as a destination: the parameter's named
    // type, or NO_SYM where it names none (a scalar, a slice, a variadic's elements).
    paramWant &self inout a:Ast at:long cn:CallNode k:long -> Sym {
        f: FnNode = a.fns.get(at);
        i: long = k;
        if (cn.receiver != NO_NODE && self.staticOwner(a, cn.receiver) == NO_SYM) { i = k + 1; }
        if (i >= f.argCount) { return NO_SYM; }
        p: VarDeclNode = a.paramAt(f, i);
        if (p.isVariadic || p.isArray) { return NO_SYM; }
        if ((p.kind == Lit.Struct || p.kind == Lit.Ref) && p.structName != NO_SYM) { return p.structName; }
        return NO_SYM;
    }

    // What `pub`, `pkg` and `local` mean at a call: callable from everywhere, from inside the
    // declaring package, and from inside the declaring file. Without this, a `local` helper of
    // another module would be reachable from anywhere that included it, which is most of the
    // program.
    //
    // Silent wherever there is no answer to give: a derived function (`clone`, `nameof`, drop
    // glue) is built with no file of its own, and a call from a global's initializer has no
    // enclosing body until `checkStmt` has found the global's own declaration.
    requireVisible &self inout a:Ast fn:Sym -> void {
        if (self.currentFile == NO_SYM) { return; }
        hit: Option<long> = self.fnAt.find(nameOf(fn));
        at: long = -1;
        match hit { Some(i) { at = i; } None { return; } }
        f: FnNode = a.fns.get(at);
        if (f.file == NO_SYM || f.visibility == Vis.Pub) { return; }
        if (f.file == self.currentFile) { return; }
        if (f.visibility == Vis.Pkg) {
            if (f.pkg == NO_SYM || f.pkg == self.currentPkg) { return; }
            failStr(format("`{}` is private to package `{}`\nhelp: declare it `pub` to call it from another package",
                           nameOf(fn), nameOf(f.pkg)));
        }
        failStr(format("`{}` is private to `{}`\nhelp: declare it `pkg` or `pub` to call it from another file",
                       nameOf(fn), nameOf(f.file)));
    }

    // A global read or written from another file, held to its visibility as a function's call is:
    // `local` (or none) is its file's own, and `pkg` its package's.
    requireGlobalVisible &self q:Sym -> void {
        if (self.currentFile == NO_SYM) { return; }
        gi: long = gReg.findGlobalSym(q);
        if (gi < 0) { return; }
        g: GlobalDef = gReg.globalDef(gi);
        if (g.file == NO_SYM || g.visibility == Vis.Pub || g.file == self.currentFile) { return; }
        if (g.visibility == Vis.Pkg) {
            if (g.pkg == NO_SYM || g.pkg == self.currentPkg) { return; }
            failStr(format("`{}` is private to package `{}`\nhelp: declare it `pub` to use it from another package",
                           nameOf(q), nameOf(g.pkg)));
        }
        failStr(format("`{}` is private to `{}`\nhelp: declare it `pkg` or `pub` to use it from another file",
                       nameOf(q), nameOf(g.file)));
    }

    // A struct stored where a different struct was declared. The store would copy the declared
    // width out of a value with another layout, so `v: Vec<long> = vecOf(1, 2, 3)` (which makes a
    // `Vec<int>`) is refused here rather than read back as garbage.
    requireSameStruct &self want:VarType got:VarType what:str -> void {
        if (want.kind != Lit.Struct || got.kind != Lit.Struct) { return; }
        if (want.structName == NO_SYM || got.structName == NO_SYM || want.structName == got.structName) { return; }
        failStr(format("mismatched types: expected `{}`, found `{}`\nnote: {} has type `{}`",
                       nameOf(want.structName), nameOf(got.structName), notePlace(what), nameOf(want.structName)));
    }

    // A `return` is a store into the function's result, held to exactly what `x: T = e` is held
    // to (`requireAssignable`). That refuses a `str` returned from `-> int`, a struct of another
    // name, a value from a `-> void` function, and nothing from one that returns something. A
    // closure written without `-> T` is not held here: its return type is whatever its body
    // returns (`settleReturn`).
    holdReturn &self inout a:Ast v:NodeId got:VarType -> void {
        if (self.curFn < 0) { return; }
        f: FnNode = a.fns.get(self.curFn);
        if (f.inferReturn) { return; }
        if (isNeverFn(f)) {
            failStr(format("`{}` is declared `-> never`, but this `return` comes back", nameOf(f.name)));
        }
        want: VarType = self.currentReturn;
        if (want.kind == Lit.Void) {
            if (v != NO_NODE && got.kind != Lit.Void) {
                failStr(format("mismatched types: expected nothing, found `{}`\nnote: `{}` returns nothing",
                               self.spellType(got.kind, got.structName), nameOf(f.name)));
            }
            return;
        }
        if (v == NO_NODE) {
            failStr(format("mismatched types: expected `{}`, found nothing\nnote: `{}` returns `{}`, and this `return` has no value",
                           self.spellType(want.kind, want.structName), nameOf(f.name), self.spellType(want.kind, want.structName)));
        }
        if (got.kind == Lit.Void && a.expr(v).op != Op.Literal) {
            failStr(format("mismatched types: expected `{}`, found nothing\nnote: `{}` returns `{}`, and this expression yields no value",
                           self.spellType(want.kind, want.structName), nameOf(f.name), self.spellType(want.kind, want.structName)));
        }
        // A `?`'s early return (`Ret.fromResidual($tryN.residual())`) where the failure made the
        // generic return type another instance: what does not fit is the failure, so say that.
        if (got.kind != want.kind || got.structName != want.structName) {
            r: NodeId = self.tryResidualArg(a, v);
            if (r != NO_NODE) {
                re: Expr = self.lentValue(a, r);
                self.refuseTryResidual(varType(re.kind, re.structName), varType(Lit.Void, NO_SYM));
            }
        }
        // Held to the language's integer rule as every store is (`narrows`), but asked here first
        // so the message can suggest `main -> long`. A returned value converts implicitly only by
        // lossless widening, and a constant has to fit, so `-> int { return n.len; }` cannot drop
        // the high half without a word.
        if (isInteger(want.kind) && isInteger(got.kind) && !canImplicitlyConvert(got.kind, want.kind)) {
            cv: Option<long> = Option.None;
            if (self.weakArg(a, v)) { cv = self.weakValue(a, v); }
            match cv {
                Some(x) {
                    if (!literalFits(x, want.kind)) {
                        failStr(format("constant `{}` out of range for `{}`\nnote: `{}` returns `{}`",
                                       x, typeName(want.kind), nameOf(f.name), typeName(want.kind)));
                    }
                }
                None {
                    failStr(format("mismatched types: expected `{}`, found `{}`\nnote: `{}` returns `{}`\nhelp: a value of type `{}` may not fit in `{}`; convert it explicitly with `as {}`{}",
                                   typeName(want.kind), typeName(got.kind), nameOf(f.name), typeName(want.kind),
                                   typeName(got.kind), typeName(want.kind), typeName(want.kind), self.mainHint(f, got.kind)));
                }
            }
        }
        self.requireAssignable(a, want, got, v, keepString(format("the return value of `{}`", nameOf(f.name))));
    }
    // The end of the narrowing help when the function is `main`, whose result type is the
    // author's to choose, so widening it is the other way out.
    mainHint &self f:FnNode got:Lit -> str {
        if (lastComponentOf(nameOf(f.name)) == "main") { return keepString(format(", or declare `main -> {}`", typeName(got))); }
        return "";
    }

    // "`long`" or "an array of `long`": a store's two sides, when one of them is an array.
    spellArrayOrNot &self t:VarType -> String {
        if (t.isArray) { return format("an array of `{}`", self.spellType(t.kind, t.structName)); }
        return format("`{}`", self.spellType(t.kind, t.structName));
    }

    // `b = a`, `b: [T; N] = a`, `S { f: a }` with `a` a whole array: `a` has to be as long as
    // the destination. `want` is the destination's length; an array literal is held elsewhere.
    requireArrayLen &self inout a:Ast want:long src:NodeId what:str -> void {
        if (want < 0 || src == NO_NODE || a.expr(src).op == Op.ArrayLit) { return; }
        got: long = self.placeArrayLen(a, src);
        if (got >= 0 && got != want) {
            failStr(format("mismatched array lengths: expected {}, found {}\nnote: {} holds {}, and a fixed array is assigned whole only from an array of the same length",
                           want, got, what, plural(want, "element")));
        }
    }

    // Whether a value of type `got` may be stored in a place of type `want`. Two structs are asked
    // by name (`requireSameStruct`); everything else differs by kind: a `str` stored in a `long`,
    // a borrow laundered into an integer, a scalar handed to a trait object. `src` is the
    // expression being stored, needed for what a type alone cannot say, such as whether it is an
    // untyped literal. `what` names the place for the note under a mismatch ("`c`", "the return
    // value of `f`").
    requireAssignable &self inout a:Ast want:VarType got:VarType src:NodeId what:str -> void {
        self.requireSameStruct(want, got, what);
        if (src == NO_NODE) { return; }
        gk: Lit = got.kind;
        if (self.adoptFloat(a, src, want.kind)) { gk = want.kind; }
        if (self.adoptWide(a, src, want.kind)) { gk = want.kind; }
        gn: Sym = got.structName;
        // Inside `unsafe`, `&x` is a raw address and may be held as one: that is the whole of
        // what the block grants. In safe code it is a lend, and laundering it into an integer is
        // refused below.
        if (self.unsafeDepth > 0 && (gk == Lit.Ref || gk == Lit.Ptr)) { return; }
        // `&x` on a struct is a lend, and a lend lives only as long as the borrow it was made
        // for. Stored in an integer it becomes an address that outlives it, which is the one
        // thing `&` in safe code promises cannot happen: `checkExpr` types every `&` as a plain
        // `long`, so without this the store reads as `long = long`. Inside `unsafe` an address is
        // an address, and the author has said so.
        if (self.unsafeDepth == 0 && self.isLend(a, src)
            && want.kind != Lit.Ref && want.kind != Lit.Struct && want.kind != Lit.TraitObj) {
            failStr(format("mismatched types: expected `{}`, found a borrow\nnote: `&` here lends a value rather than giving an address, and a borrow cannot be held past the call it was made for",
                           self.spellType(want.kind, want.structName)));
        }
        // A fixed array is a value: its element type and its length together. `kind` is the
        // element's on both sides, so an array meets only an array of the same element type here,
        // and the length is held by the caller that knows the destination's (`requireArrayLen`).
        // An array literal is held element by element where it is written. Without this,
        // `x: long = arr` or a store of another length would read whatever the store left.
        if (want.isArray || got.isArray) {
            if (a.expr(src).op == Op.ArrayLit) { return; }
            if (want.isArray != got.isArray || want.kind != got.kind || want.structName != got.structName) {
                failStr(format("mismatched types: expected {}, found {}\nnote: a fixed array is assigned only from an array of the same element type and length",
                               self.spellArrayOrNot(want), self.spellArrayOrNot(got)));
            }
            // Elements that own something cannot be copied as bytes (both arrays would release
            // them): a whole array of them is MOVED, its source left moved-from, which the
            // ownership pass writes out and refuses where no flag can record it (`ownArrayStore`).
            // A global's initializer is in no function that pass walks.
            if (want.kind == Lit.Struct && gReg.needsDrop(want.structName) && self.curFn < 0) {
                failStr(format("cannot initialize {} from another array\nnote: an array of `{}` owns what its elements hold, so it is moved rather than copied, and a global is not built by moving another array\nhelp: give it an array literal, or keep the elements in a `Vec`",
                               what, self.spellType(want.kind, want.structName)));
            }
            return;
        }
        // A concrete value stored in a trait-typed place becomes an object there, so the trait
        // has to be one. Checked here rather than at the `MakeTraitObj` that lowering reads,
        // because a declaration is where the author named the trait.
        if (want.kind == Lit.TraitObj && (gk == Lit.Struct || gk == Lit.Ref)) {
            self.requireObjectSafe(a, want.structName);
            if (gReg.hasDerives()) { self.ensureImpl(a, got.structName, want.structName, 0); }
        }
        // An untyped literal is held to the width it is stored at, which the general
        // integer-to-integer rule below does not do. The two are separable: this one is about a
        // value written in the source, not about a type inference produced.
        lv: Option<long> = self.literalValue(a, src);
        match lv {
            Some(v) {
                // Written past `long`'s maximum: a u64's, whatever it is stored in.
                wide: bool = a.expr(src).kind == Lit.U64 && v < 0;
                if (wide && want.kind != Lit.U64 && (isInteger(want.kind) || want.kind == Lit.Bool)) {
                    failStr(format("literal `{}` out of range for `{}`\nnote: only a `u64` holds it",
                                   v as u64, self.spellType(want.kind, want.structName)));
                }
                if (!wide && !literalFits(v, want.kind)) {
                    failStr(format("literal `{}` out of range for `{}`",
                                   v, self.spellType(want.kind, want.structName)));
                }
            }
            None { }
        }
        // An integer is held to the rule `canImplicitlyConvert` states: it converts implicitly only
        // by lossless widening, and a constant only when its value is one of the destination's
        // (`narrows`). Anything else is written with `as`. This relies on a callable bound saying
        // what a type parameter is first (`bindFromCallable`): otherwise `fold(xs, 0, &addLL)`
        // would make U an `int` from the literal while the step returns `long`.
        if ((isInteger(want.kind) || want.kind == Lit.Bool) && (isInteger(gk) || gk == Lit.Bool)) {
            if (self.narrows(a, want.kind, gk, src)) {
                failStr(format("mismatched types: expected `{}`, found `{}`\nnote: {} has type `{}`\nhelp: a value of type `{}` may not fit in `{}`; convert it explicitly with `as {}`",
                               typeName(want.kind), typeName(gk), notePlace(what), typeName(want.kind),
                               typeName(gk), typeName(want.kind), typeName(want.kind)));
            }
            return;
        }
        if (typeFits(want.kind, want.structName, gk, gn, self.weakArg(a, src))) { return; }
        // A distinct type and its base (or any other scalar) meet only through `as`.
        if ((want.kind == Lit.Struct && gReg.isDistinct(want.structName)) || (gk == Lit.Struct && gReg.isDistinct(gn))) {
            failStr(format("mismatched types: expected `{}`, found `{}`\nnote: a distinct type converts only with `as`\nhelp: write `x as {}`",
                           self.spellType(want.kind, want.structName), self.spellType(gk, gn),
                           self.spellType(want.kind, want.structName)));
        }
        // Two fn types that `fnSigsFit` keeps apart: a call through the place is compiled against
        // its own type, so the function stored must take the same arguments the same way.
        if (want.kind == Lit.Fn && gk == Lit.Fn) {
            failStr(format("mismatched types: expected `{}`, found `{}`\nnote: a fn value must take the same parameters, each passed the same way (lent, or given with `sink` where the type owns something), and return the same type",
                           nameOf(want.structName), nameOf(gn)));
        }
        failStr(format("mismatched types: expected `{}`, found `{}`\nnote: {} has type `{}`",
                       self.spellType(want.kind, want.structName), self.spellType(gk, gn), notePlace(what),
                       self.spellType(want.kind, want.structName)));
    }
    // A float literal (`Op.Literal` with its spelling) stored where an `f32` is wanted is an `f32`
    // literal: rounded once, from the decimal, to that width. So is arithmetic over nothing but
    // float literals (`1.1 * 2.2 + 1.1`), computed at that width throughout. Answers whether it
    // changed anything.
    adoptFloat &self inout a:Ast id:NodeId want:Lit -> bool {
        if (id == NO_NODE || want != Lit.Float || !self.floatLiteralTree(a, id)) { return false; }
        self.retypeFloatTree(a, id);
        return true;
    }

    // Arithmetic over nothing but integer literals (`1 << 40`, `65536 * 65536`) where an 8-byte
    // integer is wanted (stored in one, passed as one, or meeting one in an operation) is computed
    // at that width, as a lone literal takes the type it is handed. Computed as an `int` it would
    // wrap, and `x: long = 1 << 40` would be 0. The same goes for a shift whose left operand is
    // such arithmetic, whatever its count: a shift has its left operand's type, and
    // `m: long = 1 << k` means a `long` one. Answers whether it changed anything.
    adoptWide &self inout a:Ast id:NodeId want:Lit -> bool {
        if (id == NO_NODE || (want != Lit.Long && want != Lit.U64)) { return false; }
        e: Expr = a.expr(id);
        if (e.left == NO_NODE || e.kind == want) { return false; }
        if (self.weakArg(a, id)) {
            self.retypeIntTree(a, id, want);
            return true;
        }
        if ((e.op == Op.ShiftLeft || e.op == Op.ShiftRight) && self.weakArg(a, e.left)) {
            self.retypeIntTree(a, e.left, want);
            e.kind = want;
            a.setExpr(id, e);
            return true;
        }
        return false;
    }
    retypeIntTree &self inout a:Ast id:NodeId want:Lit -> void {
        if (id == NO_NODE) { return; }
        e: Expr = a.expr(id);
        e.kind = want;
        a.setExpr(id, e);
        if (e.left != NO_NODE) {
            self.retypeIntTree(a, e.left, want);
            self.retypeIntTree(a, e.right, want);
        }
    }

    floatLiteralTree &self inout a:Ast id:NodeId -> bool {
        if (id == NO_NODE) { return false; }
        e: Expr = a.expr(id);
        if (e.op == Op.Literal) {
            if (e.kind != Lit.Double) { return false; }
            p: Payload = e.payload;
            match p { Text(t) { return true; } _ { } }
            return false;
        }
        if (e.op == Op.Addition || e.op == Op.Subtraction || e.op == Op.Multiplication || e.op == Op.Division) {
            if (e.op == Op.Subtraction && (self.isNegationZero(a, e.left) || isNegationMark(a.expr(e.left)))) {
                return self.floatLiteralTree(a, e.right);
            }
            return self.floatLiteralTree(a, e.left) && self.floatLiteralTree(a, e.right);
        }
        return false;
    }

    retypeFloatTree &self inout a:Ast id:NodeId -> void {
        if (id == NO_NODE) { return; }
        e: Expr = a.expr(id);
        e.kind = Lit.Float;
        a.setExpr(id, e);
        if (e.op != Op.Literal) {
            self.retypeFloatTree(a, e.left);
            self.retypeFloatTree(a, e.right);
        }
    }

    // A value of one float width where the other, or an integer, is wanted, or the reverse, is
    // refused: every such conversion rounds or truncates, and is written `as`.
    holdFloat &self inout a:Ast id:NodeId want:Lit got:Lit what:str -> void {
        if (self.adoptFloat(a, id, want)) { return; }
        if (!isFloat(want) && !isFloat(got)) { return; }
        if (want == got || want == Lit.Void || got == Lit.Void || want == Lit.TypeVar || got == Lit.TypeVar) { return; }
        failStr(format("mismatched types: expected `{}`, found `{}`\nnote: {} has type `{}`\nhelp: convert it explicitly with `as {}`",
                       typeName(want), typeName(got), notePlace(what), typeName(want), typeName(want)));
    }

    // The zero the parser writes for `-x`: an integer literal 0, marked.
    isNegationZero &self inout a:Ast id:NodeId -> bool {
        if (id == NO_NODE) { return false; }
        e: Expr = a.expr(id);
        if (e.op != Op.Literal || !e.isParen || !isInteger(e.kind)) { return false; }
        p: Payload = e.payload;
        match p { Num(v) { return v == 0; } _ { } }
        return false;
    }

    retypeLeaf &self inout a:Ast id:NodeId k:Lit -> void {
        e: Expr = a.expr(id);
        e.kind = k;
        a.setExpr(id, e);
    }

    // A literal's own value, when the expression is one. `Op.Literal` and nothing else: a
    // negated literal is a unary operator over one and settles no width on its own.
    literalValue &self inout a:Ast id:NodeId -> Option<long> {
        if (id == NO_NODE) { return Option.None; }
        e: Expr = a.expr(id);
        if (e.op != Op.Literal) { return Option.None; }
        p: Payload = e.payload;
        match p { Num(v) { return Option.Some(v); } _ { } }
        return Option.None;
    }

    // The value of a weak expression (`weakArg`: a literal, or arithmetic over nothing but
    // literals), computed exactly in 64 bits, or None when it is not one or has no value (a
    // division by zero, a shift past the word).
    weakValue &self inout a:Ast id:NodeId -> Option<long> {
        if (id == NO_NODE) { return Option.None; }
        e: Expr = a.expr(id);
        if (e.left == NO_NODE) {
            if (!isWeakLiteral(e)) { return Option.None; }
            return self.literalValue(a, id);
        }
        if (isComparison(e.op) || e.op == Op.LogicalAnd || e.op == Op.LogicalOr || e.op == Op.Assignment) { return Option.None; }
        l: long = 0;
        r: long = 0;
        match self.weakValue(a, e.left) { Some(v) { l = v; } None { return Option.None; } }
        match self.weakValue(a, e.right) { Some(v) { r = v; } None { return Option.None; } }
        if (e.op == Op.Addition)       { return Option.Some(l + r); }
        if (e.op == Op.Subtraction)    { return Option.Some(l - r); }
        if (e.op == Op.Multiplication) { return Option.Some(l * r); }
        if (e.op == Op.BitwiseAnd)     { return Option.Some(l & r); }
        if (e.op == Op.BitwiseOr)      { return Option.Some(l | r); }
        if (e.op == Op.BitwiseXor)     { return Option.Some(l ^ r); }
        if (e.op == Op.Division || e.op == Op.Modulus) {
            if (r == 0) { return Option.None; }
            if (e.op == Op.Division) { return Option.Some(l / r); }
            return Option.Some(l % r);
        }
        if ((e.op == Op.ShiftLeft || e.op == Op.ShiftRight) && r >= 0 && r < 64) {
            if (e.op == Op.ShiftLeft) { return Option.Some(l << r); }
            return Option.Some(l >> r);
        }
        return Option.None;
    }

    // A literal operand `id` (or literal arithmetic) meeting a typed integer operand `other` of
    // type `want` takes that type when its value is one of `want`'s, as the untyped constant it is
    // (`b + 1` is a `u8` for `b: u8`): it is replaced by that value, a literal of `want`, so the
    // arithmetic it was written as is not redone at `want`'s width (`b + 600 / 3`). Answers
    // whether it did.
    adoptLiteral &self inout a:Ast id:NodeId own:Lit other:NodeId want:Lit -> bool {
        if (id == NO_NODE || own == want || !isInteger(want) || !self.weakArg(a, id) || self.weakArg(a, other)) { return false; }
        v: long = 0;
        match self.weakValue(a, id) { Some(x) { v = x; } None { return false; } }
        if (!literalFits(v, want)) { return false; }
        e: Expr = a.expr(id);
        a.setExpr(id, Expr { op: Op.Literal, left: NO_NODE, right: NO_NODE, kind: want, structName: NO_SYM,
                             isParen: e.isParen, payload: Payload.Num(v) });
        return true;
    }

    // Whether storing `src`, a `got`, into a place of integer type `want` narrows it: `got` does
    // not widen into `want` losslessly and `src` is no constant that is one of `want`'s values.
    // A constant that is not is refused here, said as what it is.
    narrows &self inout a:Ast want:Lit got:Lit src:NodeId -> bool {
        if (!isInteger(want) || !isInteger(got) || canImplicitlyConvert(got, want)) { return false; }
        if (src != NO_NODE && self.weakArg(a, src)) {
            match self.weakValue(a, src) {
                Some(v) {
                    if (literalFits(v, want)) { return false; }
                    failStr(format("constant `{}` out of range for `{}`", v, typeName(want)));
                }
                None { }
            }
        }
        return true;
    }

    // The variable a borrow is rooted in: the base of a field chain, the base of an index, the
    // operand of a `&`, or the receiver of the call that produced it, `v.at(0)` is a borrow of
    // `v`. NO_SYM when the root is not a plain variable, and then nothing is claimed about it.
    borrowRoot &self inout a:Ast id:NodeId depth:long -> Sym {
        if (id == NO_NODE || depth > MAX_VIEW_DEPTH) { return NO_SYM; }
        e: Expr = a.expr(id);
        p: Payload = e.payload;
        if (e.op == Op.Lvalue) {
            match p { Name(n) { return n; } _ { } }
            return NO_SYM;
        }
        match p {
            Field(f) { return self.borrowRoot(a, a.fields.get(f).base, depth + 1); }
            Index(i) {
                ix: IndexNode = a.indexes.get(i);
                if (ix.base != NO_NODE) { return self.borrowRoot(a, ix.base, depth + 1); }
                return ix.name;
            }
            Sub(v)  { return self.borrowRoot(a, v, depth + 1); }
            Call(c) { return self.borrowRoot(a, a.calls.get(c).receiver, depth + 1); }
            _ { }
        }
        return NO_SYM;
    }

    // A `&T` return hands the caller a pointer, which is sound only when what it points at
    // outlives the call. That means it was lent in: a `read` or `inout` parameter belongs to the
    // caller, and so does anything reached through one. A local dies with this frame. So does a
    // `sink` parameter. It was given away to this frame, and is released when the frame ends,
    // which is what makes `bad sink v:Vec<Res> -> &Res { return v.at(0); }` a dangling pointer
    // rather than a borrow. A global outlives everything and is always fine.
    checkReturnedBorrow &self inout a:Ast v:NodeId -> void {
        if (self.currentReturn.kind != Lit.Ref || self.curFn < 0) { return; }
        if (self.unsafeDepth > 0 || v == NO_NODE) { return; }
        root: Sym = self.borrowRoot(a, v, 0);
        if (root == NO_SYM) { return; }
        if (gReg.findGlobalSym(root) >= 0) { return; }
        conv: Conv = self.paramConvOf(a, self.curFn, root);
        if (conv == Conv.Read || conv == Conv.Inout) { return; }
        why: str = "a local of this function, which ends with the call";
        if (conv == Conv.Sink) { why = "a `sink` parameter, which this function releases when it ends"; }
        failStr(format("cannot return a borrow of `{}`\nnote: `{}` is {}\nhelp: return the value, or take the parameter as a borrow so the caller still owns it",
                       nameOf(root), nameOf(root), why));
    }

    // A place as a message names it: the variable, without the suffix shadowing gave it.
    placeName &self inout a:Ast id:NodeId -> str {
        e: Expr = a.expr(id);
        if (e.op == Op.Lvalue) {
            match e.payload {
                Name(n) {
                    nm: str = nameOf(n);
                    cut: Option<long> = strFind(nm, "$");
                    match cut { Some(i) { nm = strSlice(nm, 0, i); } None { } }
                    return keepString(format("`{}`", nm));
                }
                _ { }
            }
        }
        return "the assigned place";
    }

    // A generic struct or sum type, as opposed to a generic function: one that has methods.
    isTypeTemplate &self n:Sym -> bool {
        at: long = gReg.findTemplateSym(n);
        if (at < 0) { return false; }
        t: GTemplate = gReg.templateDef(at);
        return t.isEnum || t.fieldCount > 0;
    }

    // `Option.fromFlag(true, 5)`: `Option_fromFlag` is a method of the template, whose instances
    // each get their own copy (`Option_long_fromFlag`). Which instance this call is on is worked
    // out as a generic function's parameters are, from the template method's own parameters
    // against the arguments and its result against the destination; the instance is asked for,
    // and its copy of the method is what is called. Its result is known now, as an instantiated
    // generic function's is, though the copy is stamped only when the instance is.
    instantiateOwner &self inout a:Ast cn:CallNode st:Sym fn:Sym want:Sym -> Sym {
        hit: Option<long> = self.fnAt.find(nameOf(fn));
        at: long = -1;
        match hit { Some(i) { at = i; } None { return fn; } }
        f: FnNode = a.fns.get(at);
        t: GTemplate = gReg.templateDef(gReg.findTemplateSym(st));
        bind: HashMap<str, TypeRef>;
        for pass in 0..2 {
            k: long = 0;
            while (k < f.argCount && k < cn.argCount) {
                p: VarDeclNode = a.paramAt(f, k);
                if (!p.isVariadic && self.weakArg(a, a.argAt(cn, k)) == (pass == 1)) {
                    self.bindParam(&bind, p, self.lentValue(a, a.argAt(cn, k)), pass == 1);
                }
                k = k + 1;
            }
            if (pass == 0) { self.bindFromExpected(&bind, f, want); }
        }
        args: Vec<TypeRef>;
        s: String;
        s.pushStr(nameOf(st));
        for k in 0..t.paramCount {
            got: Option<TypeRef> = bind.find(nameOf(gReg.gParamAt(t, k)));
            b: TypeRef = typeRefOf(Lit.Void);
            match got {
                Some(x) { b = x; }
                None {
                    b = gReg.gParamDefault(t, k);
                    if (b.base == Lit.Void) {
                        failStr(format("cannot infer `{}` for the call to `{}`\nnote: no argument or destination says which `{}` it is",
                                       nameOf(gReg.gParamAt(t, k)), nameOf(fn), nameOf(st)));
                    }
                    bind.put(nameOf(gReg.gParamAt(t, k)), b);
                }
            }
            args.push(b);
            s.push('_');
            s.pushStr(typeMangleName(b.base, b.name));
        }
        inst: Sym = internString(s);
        gReg.request(st, inst, args);
        // The instance's copy of what `fn` resolved to: the template's method with the template's
        // name replaced by the instance's, as monomorphization names the clone. A method of a trait
        // this file owns carries the trait (`W_geo::Make_make` is `W_long_geo::Make_make`), and a
        // parameterized trait's arguments are this call's (`Compare_T` at T = long).
        m: Sym = methodSymbol(inst, cn.name);
        fs: str = nameOf(fn);
        ss: str = nameOf(st);
        if (fs.len > ss.len && strStartsWith(fs, ss) && charAt(fs, ss.len) == '_') {
            m = internString(format("{}{}", nameOf(inst), substTailBy(strSlice(fs, ss.len, fs.len - ss.len), bind)));
        }
        if (self.fnAt.find(nameOf(m)).isNone()) {
            r: TypeRef = self.substReturn(&bind, f.returnKind, f.returnStruct);
            if (r.name == st) { r = TypeRef { base: Lit.Struct, name: inst }; }   // the type's own name, in its block
            self.noteReturn(m, varType(r.base, r.name));
        }
        return m;
    }

    // The type a receiver names, when it names a type rather than holding a value: a bare name
    // that no variable owns and that the registry knows as a struct. NO_SYM for everything else,
    // which is the ordinary case of a method on a value.
    staticOwner &self inout a:Ast recv:NodeId -> Sym {
        if (recv == NO_NODE) { return NO_SYM; }
        e: Expr = a.expr(recv);
        if (e.op != Op.Lvalue) { return NO_SYM; }
        p: Payload = e.payload;
        n: Sym = NO_SYM;
        match p { Name(x) { n = x; } _ { return NO_SYM; } }
        if (self.lookup(n).kind != Lit.Void) { return NO_SYM; }      // a variable of that name wins
        // Already qualified: monomorphization writes the bound type's full name where a template
        // said `T`, and resolving one of those again finds nothing.
        if (gReg.hasStructSym(n)) { return n; }
        // A scalar's spelling, which is what monomorphization writes for `T.decode(inp)` at
        // T = long: its methods are `long_decode`, named from that spelling.
        if (namesScalar(nameOf(n)) && isImplableScalar(scalarNamed(nameOf(n)))) { return n; }
        // An enum of named integers has no struct row, but static methods all the same.
        if (gReg.findEnumSym(n) >= 0) { return n; }
        // Resolved from the module being checked, so a type declared here wins over one of the
        // same name imported from elsewhere: `LockGuard.new()` in a file with its own LockGuard
        // means that one, not `sync`'s.
        q: Sym = gReg.resolveBare(nameOf(self.currentModule), nameOf(n));
        if (gReg.hasStructSym(q)) { return q; }
        // A generic type named bare (`Option.fromFlag(...)`): the instance is the call's to infer.
        if (self.isTypeTemplate(n)) { return n; }
        if (self.isTypeTemplate(q)) { return q; }
        // A type alias names a type too: `AtomicInt.new(0)` is `Atomic_int_new(0)`.
        al: long = gReg.findAlias(nameOf(q));
        if (al >= 0) {
            t: TypeRef = gReg.aliasDef(al).target;
            if (t.base == Lit.Struct && gReg.hasStructSym(t.name)) { return t.name; }
        }
        return NO_SYM;
    }

    // A weak argument: a bare integer literal, or arithmetic over nothing but those. `3 * 4` is
    // as undecided as `12`, and takes the width of whatever it meets the same way.
    weakArg &self inout a:Ast id:NodeId -> bool {
        e: Expr = a.expr(id);
        if (e.left != NO_NODE) {
            if (isComparison(e.op) || e.op == Op.LogicalAnd || e.op == Op.LogicalOr || e.op == Op.Assignment) { return false; }
            return self.weakArg(a, e.left) && self.weakArg(a, e.right);
        }
        return isWeakLiteral(e);
    }

    // The destination's type against the callee's declared return: `Vec<T>` stored into a
    // `Vec<long>` says T is long. Only a type parameter nothing else bound is taken from it.
    bindFromExpected &self inout bind:HashMap<str, TypeRef> f:FnNode want:Sym -> void {
        if (want == NO_SYM) { return; }
        if (f.returnKind == Lit.TypeVar) {
            if (!bind.has(nameOf(f.returnStruct))) { bind.put(nameOf(f.returnStruct), TypeRef { base: Lit.Struct, name: want }); }
            return;
        }
        if (f.returnKind != Lit.Struct || f.returnStruct == NO_SYM) { return; }
        if (isTupleName(f.returnStruct)) {
            // Only what the arguments left open: the destination speaks after them.
            got: HashMap<str, TypeRef>;
            self.bindInstance(&got, f.returnStruct, want);
            ks: Vec<str> = got.keys();
            for j in 0..ks.len() {
                if (!bind.has(ks.get(j))) { bind.put(ks.get(j), got.get(ks.get(j))); }
            }
            return;
        }
        rp: long = gReg.findRequestSym(f.returnStruct);
        wp: long = gReg.findRequestSym(want);
        if (rp < 0 || wp < 0) { return; }
        r: GRequest = gReg.requestAt(rp);
        w: GRequest = gReg.requestAt(wp);
        if (!gReg.isPatternRequest(r) || w.base != r.base || w.argCount != r.argCount) { return; }
        for j in 0..r.argCount {
            pa: TypeRef = gReg.gArgAt(r, j);
            if (pa.base == Lit.TypeVar && !bind.has(nameOf(pa.name))) { bind.put(nameOf(pa.name), gReg.gArgAt(w, j)); }
        }
    }

    // `swap(a, b)` where `swap<T>` is generic: the instance is named by what T turned out to be,
    // which only the arguments can say. Each declared parameter is matched against the argument
    // in its place, and a parameter written as `T`, `*T`, `[T]` or `&T` binds T to what stood
    // there. Unbound parameters leave the call naming the template, which the stamped clone's
    // absence then reports honestly rather than miscompiling.
    // `off` is where the arguments start among the parameters: 1 for a method called on a value,
    // whose receiver is parameter 0 (and says nothing about the method's own type parameters).
    instantiate &self inout a:Ast cn:CallNode fn:Sym want:Sym off:long -> Sym {
        tat: long = gReg.findTemplateSym(fn);
        if (tat < 0) { return fn; }
        t: GTemplate = gReg.templateDef(tat);
        if (t.fieldCount > 0 || t.isEnum) { return fn; }        // a type, not a function
        hit: Option<long> = self.fnAt.find(nameOf(fn));
        at: long = -1;
        match hit { Some(i) { at = i; } None { return fn; } }
        f: FnNode = a.fns.get(at);

        // Two passes, because a bare integer literal is weak evidence. `6` is an `int` by
        // default but takes the width of whatever it meets, so in `binarySearchBy(&xs, 6, c)`
        // it must not out-vote the `Vec<long>` that already fixed T. Strong arguments bind
        // first; a literal then fills in only a parameter nothing else reached, which is what
        // keeps `takesT(5)` inferring int. Without the split, `key:T` would bind T = int after
        // `v:Vec<T>` had bound it long, and the body would call `Vec_int`'s methods on a
        // `Vec<long>`.
        //
        // A parameter no argument mentions (`count<T, I: Iter<T>>`, where T is named only in
        // I's bound) is read out of the bound instead. That is a fact, so it is asked at the
        // end of each pass: before a literal gets to fill anything in.
        bind: HashMap<str, TypeRef>;
        for pass in 0..2 {
            k: long = 0;
            while (k + off < f.argCount && k < cn.argCount) {
                p: VarDeclNode = a.paramAt(f, k + off);
                // `xs: ...T` collects every remaining argument, and each one stands where T does.
                if (p.isVariadic && p.elemKind == Lit.TypeVar) {
                    elem: VarDeclNode = VarDeclNode { name: p.name, kind: Lit.TypeVar, structName: p.elemStruct,
                                                      isArray: false, count: 0, conv: Conv.None, isVariadic: false,
                                                      elemKind: Lit.Void, elemStruct: NO_SYM, init: NO_NODE };
                    for j in k..cn.argCount {
                        varg: Expr = self.lentValue(a, a.argAt(cn, j));
                        if (self.weakArg(a, a.argAt(cn, j)) == (pass == 1)) { self.bindParam(&bind, elem, varg, pass == 1); }
                    }
                    k = cn.argCount;
                    continue;
                }
                arg: Expr = self.lentValue(a, a.argAt(cn, k));
                if (self.weakArg(a, a.argAt(cn, k)) == (pass == 1)) {
                    self.bindParam(&bind, p, arg, pass == 1);
                }
                k = k + 1;
            }
            self.inferThroughBounds(a, &bind, t, f);
            // What the result is stored into speaks after the strong arguments and before a
            // literal: `v: Vec<long> = vecOf(1, 2)` is a Vec<long>, and `vec![]` is inferable.
            if (pass == 0) { self.bindFromExpected(&bind, f, want); }
        }
        args: Vec<TypeRef>;
        s: String;
        s.pushStr(nameOf(fn));
        for k in 0..t.paramCount {
            got: Option<TypeRef> = bind.find(nameOf(gReg.gParamAt(t, k)));
            b: TypeRef = typeRefOf(Lit.Void);
            match got {
                Some(x) { b = x; }
                None {
                    // What nothing in the call says, the declaration may: `N: long = 4096`.
                    b = gReg.gParamDefault(t, k);
                    if (b.base == Lit.Void) {
                        failStr(format("cannot infer `{}` for the call to `{}`\nnote: no argument says what it is",
                                       nameOf(gReg.gParamAt(t, k)), nameOf(fn)));
                    }
                    bind.put(nameOf(gReg.gParamAt(t, k)), b);
                }
            }
            // A length parameter is matched only against a length's place, and a type against a
            // type's, so a mismatch here is a destination of the wrong shape: say which.
            if (gReg.gParamIsLen(t, k) != (b.base == Lit.Len)) {
                what: str = "a type";
                if (gReg.gParamIsLen(t, k)) { what = "a length"; }
                failStr(format("`{}` of `{}` is {} parameter, but this call makes it {}", nameOf(gReg.gParamAt(t, k)),
                               nameOf(fn), what, self.spellType(b.base, b.name)));
            }
            args.push(b);
            s.push('_');
            s.pushStr(typeMangleName(b.base, b.name));
        }
        // Each of the template's own bounds, held at the call where its parameters became known,
        // so `reset(5)` against `reset<T: Default>` is refused here instead of being stamped and
        // reaching the emitter as a call to an `int_new` nobody defined. It is asked here rather
        // than when the clone is stamped, because here a derive can still be run on demand
        // (`meetsBound`) and a fn value or closure is typed. The bounds are on the function's
        // node: a generic function's own, or a method's own type parameters' (an instance's copy
        // of a method takes them from the method's template).
        bFirst: long = f.firstBound;
        bCount: long = f.boundCount;
        for b in 0..bCount {
            mb: MethodBound = gReg.boundAt(bFirst + b);
            if (mb.param < 0 || mb.param >= args.len()) { continue; }
            arg: TypeRef = args.get(mb.param);
            if (!self.boundHolds(a, arg, mb.trait)) {
                tn: String = spellTypeRef(TypeRef { base: Lit.Struct, name: mb.trait.name });
                failStr(format("`{}` does not implement `{}`\nnote: required by the bound `{}: {}` on `{}`",
                               self.spellType(arg.base, arg.name), keepString(tn),
                               nameOf(gReg.gParamAt(t, mb.param)), keepString(tn), nameOf(fn)));
            }
        }
        inst: Sym = internString(s);
        self.wanted.push(FnRequest { base: fn, instance: inst,
                                     firstArg: gReg.addGenericArgs(args), argCount: args.len() });
        noteOrigin(inst, gPos, self.instanceLabel(fn, args));
        // What it returns has to be known now, not when the clone is checked next round:
        // `search(v, x).isSome()` is one expression, and the receiver of that `.isSome()` is this
        // call's result.
        r: TypeRef = self.substReturn(&bind, f.returnKind, f.returnStruct);
        self.noteReturn(inst, varType(r.base, r.name));
        return inst;
    }

    // Whether `t` meets the bound `tr` at a generic call. What the rest of the compile cannot see
    // yet is taken to hold and left to the stamped body: a type parameter, an instance not laid out.
    // A callable bound (`F: Fn(A) -> R`) holds for a fn value, a closure and an `Fn` object; `Eq`
    // for anything `==` compares (a scalar, a `str`, a struct whose `Eq` is written or derivable);
    // `Copy`, `Clone` and a written or derived implementation as monomorphization decides them.
    boundHolds &self inout a:Ast t:TypeRef tr:TraitRef -> bool {
        bare: str = lastComponentOf(nameOf(tr.name));
        if (t.base == Lit.TypeVar || t.base == Lit.Void) { return true; }
        base: TypeRef = t;
        if (t.base == Lit.Ref) { base = TypeRef { base: Lit.Struct, name: t.name }; }
        if (isCoreTraitName(bare) && strStartsWith(bare, "Fn")) {
            if (base.base == Lit.Fn || base.base == Lit.TraitObj) { return true; }
            if (base.base != Lit.Struct) { return false; }
            return gReg.findStructSym(base.name) < 0
                || self.fnNames.has(nameOf(methodSymbol(base.name, intern("call"))));
        }
        if (base.base == Lit.Struct && !namedScalar(base.base, base.name)
            && gReg.findStructSym(base.name) < 0 && gReg.findEnumSym(base.name) < 0) { return true; }
        if (bare == "Eq") {
            if (base.base != Lit.Struct || namedScalar(base.base, base.name)) { return true; }
            if (gReg.structImplements(nameOf(base.name), tr.name)) { return true; }
            return self.canDeriveEq(base.name, 0);
        }
        return self.meetsBound(a, base, tr.name, 0);
    }

    // How a note names a generic function's instance: `vecOf<long>`.
    instanceLabel &self fn:Sym args:Vec<TypeRef> -> Sym {
        s: String;
        s.pushStr(nameOf(fn));
        s.push('<');
        for k in 0..args.len() {
            if (k > 0) { s.pushStr(", "); }
            s.pushString(spellTypeRef(args.get(k)));
        }
        s.push('>');
        return internString(s);
    }

    // A template's declared return type under the bindings a call inferred. A bare `T` is what T
    // turned out to be; `Option<T>` is that template at the bound arguments, which has to be
    // requested as well as named, since the type did not exist until this call asked for it.
    substReturn &self inout bind:HashMap<str, TypeRef> k:Lit n:Sym -> TypeRef {
        if (k == Lit.TypeVar) {
            hit: Option<TypeRef> = bind.find(nameOf(n));
            match hit { Some(b) { return b; } None { } }
            return TypeRef { base: k, name: n };
        }
        if (n == NO_SYM) { return TypeRef { base: k, name: n }; }
        // `(B, A)` is the tuple of what B and A turned out to be.
        if (k == Lit.Struct && isTupleName(n)) {
            elems: Vec<TypeRef> = tupleElems(n);
            changed: bool = false;
            for j in 0..elems.len() {
                pe: TypeRef = elems.get(j);
                c: TypeRef = self.substReturn(bind, pe.base, pe.name);
                if (c.base == Lit.TypeVar) { return TypeRef { base: k, name: n }; }
                if (c.base != pe.base || c.name != pe.name) { changed = true; elems.set(j, c); }
            }
            if (!changed) { return TypeRef { base: k, name: n }; }
            return TypeRef { base: k, name: registerTuple(elems) };
        }
        at: long = gReg.findRequestSym(n);
        if (at < 0) { return TypeRef { base: k, name: n }; }
        r: GRequest = gReg.requestAt(at);
        if (!gReg.isPatternRequest(r)) { return TypeRef { base: k, name: n }; }
        args: Vec<TypeRef>;
        s: String;
        s.pushStr(nameOf(r.base));
        for j in 0..r.argCount {
            pa: TypeRef = gReg.gArgAt(r, j);
            c: TypeRef = self.substReturn(bind, pa.base, pa.name);
            if (c.base == Lit.TypeVar) { return TypeRef { base: k, name: n }; }
            args.push(c);
            s.push('_');
            s.pushStr(typeMangleName(c.base, c.name));
        }
        inst: Sym = internString(s);
        gReg.request(r.base, inst, args);
        return TypeRef { base: k, name: inst };
    }

    // `x: T;` with no initializer, where T says how to make one: the declaration constructs.
    // That is what `Default` is for: a type that can be built from nothing is built, rather than
    // left as whatever the stack or the `.data` section happened to hold. A type without it stays
    // uninitialized, which the definite-init check is there to catch.
    defaultInit &self inout a:Ast at:long d:VarDeclNode -> void {
        // ...unless the very next statement stores into it. Building a value there and then
        // overwriting it releases the built one, which is a visible drop nobody asked for.
        if (self.noDefault) { return; }
        if (d.isArray || d.kind != Lit.Struct || d.structName == NO_SYM) { return; }
        if (!gReg.structImplements(nameOf(d.structName), intern("Default"))) { return; }
        ctor: Sym = methodSymbol(d.structName, intern("new"));
        if (!self.fnNames.has(nameOf(ctor))) { return; }
        a.calls.push(CallNode { name: self.resolveFn(ctor), receiver: NO_NODE,
                                firstArg: 0, argCount: 0, slot: NO_SLOT, callee: NO_NODE, sigKey: NO_SYM });
        init: NodeId = a.leafOf(Op.FunctionCall, Payload.Call(a.calls.len() - 1),
                                Lit.Struct, d.structName);
        d.init = init;
        a.decls.set(at, d);
    }

    // `with x { ... }`: a scoped wrapper. `x.hold()` returns a guard, the body runs, and the
    // guard is released when the block is left. Written out here as an ordinary block so that
    // nothing downstream has to know `with` exists:
    //
    //     { g: G = x.hold();  <body> }
    //
    // The guard is a local like any other, so its release is the ordinary drop at the end of its
    // scope, which ownership places on every way out of the block: the end, a `break` or a
    // `continue`, a `return` or a `?`, and a `raise` that a `recover` around it catches. A drop
    // written out here as well would release the guard a second time.
    desugarWith &self inout a:Ast at:long -> void {
        w: WithNode = a.withs.get(at);
        x: VarType = self.lookup(self.resolveVar(w.name));
        if (x.kind != Lit.Struct || x.structName == NO_SYM) {
            failStr(format("cannot use `{}` in `with`\nnote: `with` needs a wrapper struct", nameOf(w.name)));
        }
        hold: Sym = self.resolveFn(methodSymbol(x.structName, intern("hold")));
        g: VarType = self.returnOf(hold);
        if (g.kind != Lit.Struct || g.structName == NO_SYM) {
            failStr(format("cannot use `{}` in `with`\nnote: its type `{}` has no `hold()` that returns a guard",
                           nameOf(w.name), nameOf(x.structName)));
        }
        // A guard with no Drop would make `with` a no-op that quietly holds the lock forever, so
        // its absence is an error rather than something to skip.
        if (!self.fnNames.has(nameOf(methodSymbol(g.structName, intern("drop"))))) {
            failStr(format("the guard `{}` that `{}.hold()` returns does not implement `Drop`\nnote: `with` releases the guard by dropping it, so without `Drop` it would never be released",
                           nameOf(g.structName), nameOf(x.structName)));
        }

        // g: G = x.hold();
        recv: NodeId = a.leafOf(Op.Lvalue, Payload.Name(self.resolveVar(w.name)),
                                Lit.Struct, x.structName);
        // The bare name: this is a method call like any other, and checking the block below is
        // what turns it into `Mutex_..._hold`. Writing the resolved name here would have the
        // owner prepended to it a second time.
        a.calls.push(CallNode { name: intern("hold"), receiver: recv, firstArg: 0, argCount: 0,
                                slot: NO_SLOT, callee: NO_NODE, sigKey: NO_SYM });
        self.withHolds.put(a.calls.len() - 1, true);
        call: NodeId = a.leafOf(Op.MethodCall, Payload.Call(a.calls.len() - 1),
                                Lit.Struct, g.structName);
        gname: Sym = internString(format("$guard{}", self.guards));
        self.guards = self.guards + 1;
        // A guard that projects (one with `at`/`get` and `set`) stands in for the wrapper
        // inside the body: a read of `x` is a read of what it guards, and a write to `x` writes
        // through it. A hold-only guard (a lock) has neither, and the body uses `x` as written.
        reader: str = "at";
        if (!self.fnNames.has(nameOf(methodSymbol(g.structName, intern("at"))))) { reader = "get"; }
        if (self.fnNames.has(nameOf(methodSymbol(g.structName, intern(reader))))
            && self.fnNames.has(nameOf(methodSymbol(g.structName, intern("set"))))) {
            self.projectBlock(a, w.body, self.resolveVar(w.name), gname, intern(reader));
        }
        a.decls.push(VarDeclNode { name: gname, kind: Lit.Struct, structName: g.structName,
                                   isArray: false, count: 0, conv: Conv.None, isVariadic: false,
                                   elemKind: Lit.Void, elemStruct: NO_SYM, init: call });
        ids: Vec<long>;
        ids.push(a.addStmt(StmtKind.VarDecl, a.decls.len() - 1));

        n: long = a.blockLen(w.body);
        for k in 0..n { ids.push(a.stmtRuns.get(a.blocks.get(w.body).firstStmt + k)); }

        // The rewritten run replaces the `with`'s body, so the node stays a `With` and the
        // lowerer runs it as the block it now is.
        a.withs.set(at, WithNode { name: w.name, body: a.addBlock(ids) });
        self.checkBlock(a, a.withs.get(at).body);
    }

    // Rewrite every mention of the guarded variable in a `with` body: a read becomes `g.at()`,
    // an assignment becomes `g.set(v)`. Done in place, because the nodes are already wired into
    // their parents and only what they mean changes.
    projectBlock &self inout a:Ast b:long x:Sym g:Sym reader:Sym -> void {
        n: long = a.blockLen(b);
        for k in 0..n { self.projectStmt(a, a.stmtAt(b, k), x, g, reader); }
    }

    projectStmt &self inout a:Ast st:Stmt x:Sym g:Sym reader:Sym -> void {
        if (st.kind == StmtKind.Expr || st.kind == StmtKind.Call) {
            self.projectExpr(a, a.exprStmts.get(st.at).value, x, g, reader);
        } else if (st.kind == StmtKind.Return) {
            self.projectExpr(a, a.returns.get(st.at).value, x, g, reader);
        } else if (st.kind == StmtKind.VarDecl) {
            self.projectExpr(a, a.decls.get(st.at).init, x, g, reader);
        } else if (st.kind == StmtKind.If) {
            f: long = st.at;
            while (f >= 0) {
                nd: IfNode = a.ifs.get(f);
                self.projectExpr(a, nd.cond, x, g, reader);
                self.projectBlock(a, nd.body, x, g, reader);
                f = nd.elseIf;
            }
        } else if (st.kind == StmtKind.While || st.kind == StmtKind.Recover) {
            wn: WhileNode = a.whiles.get(st.at);
            self.projectExpr(a, wn.cond, x, g, reader);
            self.projectBlock(a, wn.body, x, g, reader);
            if (wn.step >= 0) { self.projectBlock(a, wn.step, x, g, reader); }
        } else if (st.kind == StmtKind.Loop || st.kind == StmtKind.Unsafe
                   || st.kind == StmtKind.Block) {
            self.projectBlock(a, a.blockStmts.get(st.at).body, x, g, reader);
        } else if (st.kind == StmtKind.With) {
            self.projectBlock(a, a.withs.get(st.at).body, x, g, reader);
        } else if (st.kind == StmtKind.Match) {
            m: MatchNode = a.matches.get(st.at);
            for k in 0..m.armCount {
                self.projectBlock(a, a.arms.get(m.firstArm + k).body, x, g, reader);
            }
        }
    }

    // An expression, in place. An assignment to the guarded variable is caught before its own
    // left operand is visited: the target is being written, not read.
    projectExpr &self inout a:Ast id:NodeId x:Sym g:Sym reader:Sym -> void {
        if (id == NO_NODE) { return; }
        e: Expr = a.expr(id);
        if (e.op == Op.Assignment && self.namesVar(a, e.left, x)) {
            self.projectExpr(a, e.right, x, g, reader);
            args: Vec<NodeId>;
            args.push(e.right);
            self.guardCall(a, id, g, intern("set"), args);
            return;
        }
        if (e.op == Op.Lvalue && self.namesVar(a, id, x)) {
            args: Vec<NodeId>;
            self.guardCall(a, id, g, reader, args);
            return;
        }
        // `&x` inside the body has nothing to point at: within the block `x` names the value the
        // guard holds, reached through `get()`/`set()`, and it has no address of its own. The
        // `Sub` arm below would rewrite the operand to `g.get()` and leave the `&` taking the
        // address of that temporary, which would compile cleanly and crash. A name that cannot
        // be lent has to say so.
        if (e.op == Op.AddressOf) {
            p0: Payload = e.payload;
            match p0 {
                Sub(v) {
                    if (self.namesVar(a, v, x)) {
                        failStr(format("cannot take the address of `{}` inside `with`\nnote: inside the block it names the value the guard holds, which has no address of its own",
                                       nameOf(x)));
                    }
                }
                _ { }
            }
        }
        self.projectExpr(a, e.left, x, g, reader);
        self.projectExpr(a, e.right, x, g, reader);
        p: Payload = e.payload;
        match p {
            Sub(v)   { self.projectExpr(a, v, x, g, reader); }
            Field(f) { self.projectExpr(a, a.fields.get(f).base, x, g, reader); }
            Index(i) {
                ix: IndexNode = a.indexes.get(i);
                self.projectExpr(a, ix.base, x, g, reader);
                self.projectExpr(a, ix.index, x, g, reader);
            }
            Call(c) {
                cn: CallNode = a.calls.get(c);
                self.projectExpr(a, cn.receiver, x, g, reader);
                for k in 0..cn.argCount { self.projectExpr(a, a.argAt(cn, k), x, g, reader); }
            }
            Lit(l) {
                ln: LitNode = a.lits.get(l);
                for k in 0..ln.initCount {
                    self.projectExpr(a, a.inits.get(ln.firstInit + k).value, x, g, reader);
                }
                self.projectExpr(a, ln.rest, x, g, reader);
            }
            _ { }
        }
    }

    namesVar &self inout a:Ast id:NodeId x:Sym -> bool {
        if (id == NO_NODE) { return false; }
        e: Expr = a.expr(id);
        if (e.op != Op.Lvalue) { return false; }
        p: Payload = e.payload;
        match p { Name(n) { return n == x; } _ { } }
        return false;
    }

    // Turn the node at `id` into `g.<method>(args)`, in place.
    guardCall &self inout a:Ast id:NodeId g:Sym method:Sym args:Vec<NodeId> -> void {
        recv: NodeId = a.leafOf(Op.Lvalue, Payload.Name(g), Lit.Struct, NO_SYM);
        a.calls.push(CallNode { name: method, receiver: recv, firstArg: a.addArgs(args),
                                argCount: args.len(), slot: NO_SLOT, callee: NO_NODE, sigKey: NO_SYM });
        a.setExpr(id, Expr { op: Op.MethodCall, left: NO_NODE, right: NO_NODE, kind: Lit.Void,
                             structName: NO_SYM, isParen: false,
                             payload: Payload.Call(a.calls.len() - 1) });
    }

    // Whether a block can leave its function through a `return` (a `?` is one by now) anywhere
    // inside it.
    blockReturns &self inout a:Ast b:long -> bool {
        n: long = a.blockLen(b);
        for k in 0..n {
            st: Stmt = a.stmtAt(b, k);
            if (st.kind == StmtKind.Return) { return true; }
            if (st.kind == StmtKind.If) {
                f: IfNode = a.ifs.get(st.at);
                if (self.blockReturns(a, f.body)) { return true; }
                if (f.elseIf >= 0 && self.ifReturns(a, f.elseIf)) { return true; }
            }
            if (st.kind == StmtKind.While) {
                if (self.blockReturns(a, a.whiles.get(st.at).body)) { return true; }
            }
            if (st.kind == StmtKind.Recover) {
                if (self.blockReturns(a, a.whiles.get(st.at).body)) { return true; }
                if (self.blockReturns(a, a.whiles.get(st.at).step)) { return true; }
            }
            if (st.kind == StmtKind.Loop || st.kind == StmtKind.Unsafe
                || st.kind == StmtKind.Block) {
                if (self.blockReturns(a, a.blockStmts.get(st.at).body)) { return true; }
            }
            if (st.kind == StmtKind.With) {
                if (self.blockReturns(a, a.withs.get(st.at).body)) { return true; }
            }
            // A `return` in an arm. Without this, a function whose every path returns from inside
            // a `match` (`BufWriter.due`) would count as never returning, and the back end
            // believes that: code after a call to one is deleted (`Instr.noReturn`).
            if (st.kind == StmtKind.Match) {
                m: MatchNode = a.matches.get(st.at);
                for j in 0..m.armCount {
                    if (self.blockReturns(a, a.arms.get(m.firstArm + j).body)) { return true; }
                }
            }
        }
        return false;
    }

    ifReturns &self inout a:Ast at:long -> bool {
        f: IfNode = a.ifs.get(at);
        if (self.blockReturns(a, f.body)) { return true; }
        if (f.elseIf >= 0) { return self.ifReturns(a, f.elseIf); }
        return false;
    }

    // Whether control can fall off the end of this block: the question a non-void function has
    // to answer no to. `blockReturns` above asks whether a return is reachable, which is the
    // opposite question and the wrong one here: a return inside an `if` with no `else` is
    // reachable and still leaves a path that falls through.
    //
    // A path that cannot fall through is a `return`, an infinite `loop`, or a call to something
    // that never comes back (`divergingCall`). Everything else is walked to its last statement,
    // since only the last one can be what the function ends on.
    alwaysExits &self inout a:Ast b:long -> bool {
        n: long = a.blockLen(b);
        for k in 0..n {
            if (self.stmtExits(a, a.stmtAt(b, k))) { return true; }
        }
        return false;
    }

    stmtExits &self inout a:Ast st:Stmt -> bool {
        if (st.kind == StmtKind.Return) { return true; }
        if (st.kind == StmtKind.If) { return self.ifExits(a, st.at); }
        // A `loop` with no `break` never ends, so nothing after it runs. A `while` may run zero
        // times, so it never settles the question.
        if (st.kind == StmtKind.Loop) {
            return !self.blockBreaks(a, a.blockStmts.get(st.at).body);
        }
        if (st.kind == StmtKind.Unsafe || st.kind == StmtKind.Block) {
            return self.alwaysExits(a, a.blockStmts.get(st.at).body);
        }
        // A `with` body that exits takes its guard's release with it; the desugar puts the
        // release before the return, and a `return` out of one is refused elsewhere.
        // A `raise` under the body lands in the handler, so both have to.
        if (st.kind == StmtKind.Recover) {
            return self.alwaysExits(a, a.whiles.get(st.at).body) && self.alwaysExits(a, a.whiles.get(st.at).step);
        }
        if (st.kind == StmtKind.With) { return self.alwaysExits(a, a.withs.get(st.at).body); }
        // Every arm, or it is not settled, and a `match` is exhaustive, so every arm is every
        // path.
        if (st.kind == StmtKind.Match) {
            m: MatchNode = a.matches.get(st.at);
            if (m.armCount == 0) { return false; }
            for k in 0..m.armCount {
                if (!self.alwaysExits(a, a.arms.get(m.firstArm + k).body)) { return false; }
            }
            return true;
        }
        if (st.kind == StmtKind.Expr) { return self.divergingCall(a, a.exprStmts.get(st.at).value); }
        if (st.kind == StmtKind.Asm) { return a.asms.get(st.at).noReturn; }
        return false;
    }

    // A statement that does not come back by declaration: a call to a `-> never` function, or an
    // `asm -> never` block. What the per-function walks (definite initialization, ownership) end
    // a path on. (The return check also takes what a fixpoint finds always diverging,
    // `divergingCall`.)
    neverStmt &self inout a:Ast st:Stmt -> bool {
        if (st.kind == StmtKind.Asm) { return a.asms.get(st.at).noReturn; }
        if (st.kind != StmtKind.Expr && st.kind != StmtKind.Call) { return false; }
        return self.neverCall(a, a.exprStmts.get(st.at).value);
    }
    neverCall &self inout a:Ast id:NodeId -> bool {
        if (id == NO_NODE) { return false; }
        e: Expr = a.expr(id);
        if (e.op != Op.FunctionCall && e.op != Op.MethodCall) { return false; }
        p: Payload = e.payload;
        match p {
            Call(c) {
                at: long = self.fnNodeOf(a.calls.get(c).name);
                return at >= 0 && isNeverFn(a.fns.get(at));
            }
            _ { }
        }
        return false;
    }

    // An if-chain settles the question only when every link's body does and the chain ends in a
    // bare `else`: without one there is a path where no branch was taken. The parser writes a
    // bare `else` as a link whose condition is the literal `true` and whose chain ends there.
    ifExits &self inout a:Ast at:long -> bool {
        f: IfNode = a.ifs.get(at);
        if (!self.alwaysExits(a, f.body)) { return false; }
        if (f.elseIf >= 0) { return self.ifExits(a, f.elseIf); }
        return isAlwaysTrue(a.expr(f.cond));
    }

    // Whether a `break` can leave this loop. A nested loop's own break belongs to it, so the
    // walk does not descend into one.
    blockBreaks &self inout a:Ast b:long -> bool {
        n: long = a.blockLen(b);
        for k in 0..n {
            st: Stmt = a.stmtAt(b, k);
            if (st.kind == StmtKind.Break) { return true; }
            if (st.kind == StmtKind.If) {
                if (self.ifBreaks(a, st.at)) { return true; }
                continue;
            }
            if (st.kind == StmtKind.Unsafe || st.kind == StmtKind.Block) {
                if (self.blockBreaks(a, a.blockStmts.get(st.at).body)) { return true; }
                continue;
            }
            if (st.kind == StmtKind.With) {
                if (self.blockBreaks(a, a.withs.get(st.at).body)) { return true; }
                continue;
            }
            if (st.kind == StmtKind.Recover) {
                if (self.blockBreaks(a, a.whiles.get(st.at).body)) { return true; }
                if (self.blockBreaks(a, a.whiles.get(st.at).step)) { return true; }
                continue;
            }
            if (st.kind == StmtKind.Match) {
                m: MatchNode = a.matches.get(st.at);
                for j in 0..m.armCount {
                    if (self.blockBreaks(a, a.arms.get(m.firstArm + j).body)) { return true; }
                }
            }
        }
        return false;
    }

    ifBreaks &self inout a:Ast at:long -> bool {
        f: IfNode = a.ifs.get(at);
        if (self.blockBreaks(a, f.body)) { return true; }
        if (f.elseIf >= 0) { return self.ifBreaks(a, f.elseIf); }
        return false;
    }

    // A statement that is a call to a function that never returns: declared `-> never`, or found
    // by the fixpoint in `checkReturns` (a function whose own body always exits by one of these
    // is one of them too).
    divergingCall &self inout a:Ast id:NodeId -> bool {
        if (id == NO_NODE) { return false; }
        e: Expr = a.expr(id);
        if (e.op != Op.FunctionCall && e.op != Op.MethodCall) { return false; }
        p: Payload = e.payload;
        match p {
            Call(c) {
                n: str = nameOf(a.calls.get(c).name);
                return self.diverging.has(n) || self.neverCall(a, id);
            }
            _ { }
        }
        return false;
    }

    // Whether a value of this type is, or contains, a borrowed view.
    //
    // A trait object is {data, vtable}: a pointer to something it does not own. A closure is one
    // too: its `Fn(..)` type is a trait object over the capture struct sitting in the frame that
    // made it. And a struct holding one is a view of that same frame, which is why this follows
    // fields rather than stopping at the type: `Keep<Fn(long)->long>` is as unable to leave the
    // frame as the closure inside it.
    holdsView &self k:Lit n:Sym depth:long -> bool {
        if (k == Lit.TraitObj) { return true; }
        if (k != Lit.Struct || n == NO_SYM || depth > MAX_VIEW_DEPTH) { return false; }
        at: long = gReg.findStructSym(n);
        if (at < 0) { return false; }
        d: StructDef = gReg.structDef(at);
        for i in 0..d.fieldCount {
            f: FieldDef = gReg.fieldAt(d, i);
            if (self.holdsView(f.kind, f.structName, depth + 1)) { return true; }
        }
        return false;
    }

    // A safe function may not hand a borrowed view back to its caller: the frame it points into
    // is the one being left. An `unsafe` function may. There the caller has vouched for it.
    checkReturnedViews &self inout a:Ast -> void {
        i: long = 0;
        while (i < a.fns.len()) {
            f: FnNode = a.fns.get(i);
            i = i + 1;
            if (f.isUnsafe || f.isTemplate || f.body < 0 || isExternFn(i - 1) || isUnchecked(i - 1)) { continue; }
            if (!self.holdsView(f.returnKind, f.returnStruct, 0)) { continue; }
            what: str = "a borrowed view";
            if (f.returnKind != Lit.TraitObj) { what = "a value holding a borrowed view"; }
            self.atFn(a, i - 1);
            failStr(format("cannot return {} of type `{}` from `{}`\nnote: it points into the frame the function returns from\nhelp: return the concrete type, or declare the function `unsafe` to vouch for it",
                           what, self.spellType(f.returnKind, f.returnStruct), nameOf(f.name)));
        }
    }

    // A `str`, a slice, a trait object and a fn value are views: what the closure captures is the
    // handle, copied, so assigning to it inside the body changes the copy and nothing outside.
    // Left alone, the write would compile and do nothing, which is worse than either a write that
    // works or a refusal.
    //
    // A captured struct is not one of these (it is captured as the value it is), so only the
    // four handle kinds are refused. `capturesMutably` answers which captures a body writes; the
    // exclusivity check asks it too.
    checkCapturedWrites &self inout a:Ast -> void {
        for i in 0..gReg.structCount() {
            d: StructDef = gReg.structDef(i);
            if (!isClosureStruct(d.name)) { continue; }
            // A dependency's closure was held to this by its own compile; its body is not
            // checked here.
            if (isExternFn(self.fnNodeOf(methodName(d.name, intern("call"))))) { continue; }
            for k in 0..d.fieldCount {
                f: FieldDef = gReg.fieldAt(d, k);
                if (!(f.kind == Lit.Str || f.kind == Lit.Slice
                      || f.kind == Lit.TraitObj || f.kind == Lit.Fn)) { continue; }
                if (!self.capturesMutably(a, d.name, f.name)) { continue; }
                self.atFn(a, self.fnNodeOf(methodName(d.name, intern("call"))));
                failStr(format("cannot assign to the captured `{}` inside a closure\nnote: a closure captures a `{}` by value, so the write would change only its own copy",
                               nameOf(f.name), typeName(f.kind)));
            }
        }
    }

    // An implementation hands each parameter over the way its trait says it does.
    //
    // A caller reaching the method through an object knows only the trait: it reads the contract
    // to decide whether it still owns what it passed. So a trait that lends `r` and an impl that
    // consumes it disagree about exactly one thing (who releases) and the caller releases what
    // the implementation already did. The same disagreement `enforceFnRef` reports for a function
    // pointer, which is the same problem read through a different kind of handle.
    //
    // Only where the type owns something: with nothing to release, the difference is whether the
    // callee copies, and either is fine.
    checkImplConventions &self inout a:Ast -> void {
        for i in 0..gReg.implCount() {
            im: TraitImplDef = gReg.implAt(i);
            tat: long = gReg.findTraitSym(im.trait.name);
            if (tat < 0) { continue; }
            t: TraitDef = gReg.traitDef(tat);
            for m in 0..t.methodCount {
                sig: TraitMethodSig = gReg.traitMethodAt(t, m);
                hit: Option<long> = self.fnAt.find(nameOf(implMethodName(im, sig.name)));
                at: long = -1;
                match hit { Some(x) { at = x; } None { continue; } }
                if (isUnchecked(at)) { continue; }      // held to this where it was first stamped, or compiled
                f: FnNode = a.fns.get(at);
                k: long = 0;
                while (k < sig.paramCount && k + 1 < f.argCount) {
                    want: VarDeclNode = a.decls.get(a.params.get(sig.firstParam + k));
                    have: VarDeclNode = a.paramAt(f, k + 1);
                    idx: long = k;
                    k = k + 1;
                    // `inout` is the contract too: a caller through the trait lends (or does not
                    // lend) by the trait's word, and the guard and the exclusivity check take the
                    // trait's word for whether the call writes what it passes.
                    if ((want.conv == Conv.Inout) != (have.conv == Conv.Inout)) {
                        self.atFn(a, at);
                        if (want.conv == Conv.Inout) {
                            failStr(format("method `{}` has an incompatible signature for trait `{}`\nnote: the trait lends parameter {} (`{}`) `inout`, and this implementation does not\nhelp: declare it `inout`",
                                           nameOf(f.name), nameOf(im.trait.name), idx, nameOf(want.name)));
                        }
                        failStr(format("method `{}` has an incompatible signature for trait `{}`\nnote: this implementation declares parameter {} (`{}`) `inout`, and the trait does not, so a caller through the trait would not know it is written\nhelp: declare it `inout` in the trait",
                                       nameOf(f.name), nameOf(im.trait.name), idx, nameOf(want.name)));
                    }
                    if (want.kind != Lit.Struct && want.kind != Lit.Ref) { continue; }
                    if (want.structName == NO_SYM || nameOf(want.structName) == "Self") { continue; }
                    if (!gReg.needsDrop(want.structName)) { continue; }
                    if ((want.conv == Conv.Sink) == (have.conv == Conv.Sink)) { continue; }
                    verb: str = "lends";
                    fix:  str = "drop the `sink`";
                    if (want.conv == Conv.Sink) { verb = "takes"; fix = "declare it `sink`"; }
                    self.atFn(a, at);
                    failStr(format("method `{}` has an incompatible signature for trait `{}`\nnote: the trait {} parameter {} (`{}`), and this implementation does not\nhelp: {}",
                                   nameOf(f.name), nameOf(im.trait.name), verb, idx,
                                   nameOf(want.name), fix));
                }
            }
        }
    }

    // Every non-void function ends on a `return`, or on something that never comes back.
    //
    // Run once, after the middle end has settled, rather than beside each body as it is checked:
    // divergence is a property of the whole program, `Option.unwrap` ends its `None` arm with
    // `trapNone()`, and whether that returns depends on a function declared below it and, for a
    // stamped generic, cloned several rounds later. Asking during the walk would answer from
    // whatever half of the program had been seen.
    checkReturns &self inout a:Ast -> void {
        // A dependency's functions diverge or not as its own compile found: their bodies are not
        // walked here, and its facts say which never come back.
        for i0 in 0..a.fns.len() {
            if (isExternFn(i0)) {
                fi: long = fnFactOf(i0);
                if (fi >= 0 && gFacts.fns.get(fi).divergent) { self.diverging.put(nameOf(a.fns.get(i0).name), true); }
            }
            // Declared `-> never`: diverging by its declaration, which the body is held to below.
            if (isNeverFn(a.fns.get(i0))) { self.diverging.put(nameOf(a.fns.get(i0).name), true); }
        }
        self.holdDeclarations(a);
        // The diverging set, to a fixpoint over the whole program. A function diverges when no
        // path through it reaches a `return` and every path ends in something that does not come
        // back. One more round adds the callers of what the last round found.
        rounds: long = 0;
        while (rounds < MAX_DIVERGE_ROUNDS) {
            added: long = 0;
            i: long = 0;
            while (i < a.fns.len()) {
                f: FnNode = a.fns.get(i);
                i = i + 1;
                if (f.isTemplate || f.body < 0 || isExternFn(i - 1) || isUnchecked(i - 1)) { continue; }
                if (self.diverging.has(nameOf(f.name))) { continue; }
                if (self.blockReturns(a, f.body)) { continue; }
                if (!self.alwaysExits(a, f.body)) { continue; }
                self.diverging.put(nameOf(f.name), true);
                added = added + 1;
            }
            if (added == 0) { rounds = MAX_DIVERGE_ROUNDS; } else { rounds = rounds + 1; }
        }
        // The global outlives this checker, so it keeps the interner's copy of each name.
        gNoReturnFns.clear();
        names: Vec<str> = self.diverging.keys();
        for n in names { gNoReturnFns.put(keep(n), true); }
        i: long = 0;
        while (i < a.fns.len()) {
            f: FnNode = a.fns.get(i);
            i = i + 1;
            if (f.isTemplate || f.body < 0 || isExternFn(i - 1) || isUnchecked(i - 1)) { continue; }
            // `-> never`: no path may reach the end (a `return` in one was refused where it stood).
            if (isNeverFn(f) && !self.alwaysExits(a, f.body)) {
                self.atFn(a, i - 1);
                failStr(format("control can reach the end of `{}`, which is declared `-> never`\nhelp: end every path with a call to a `-> never` function, an endless `loop`, or an `asm -> never` block",
                               nameOf(f.name)));
            }
            if (f.returnKind == Lit.Void) { continue; }
            if (self.alwaysExits(a, f.body)) { continue; }
            self.atFn(a, i - 1);
            failStr(format("missing `return` at the end of `{}`\nnote: `{}` returns `{}`, and control can reach the end of its body",
                           nameOf(f.name), nameOf(f.name), self.spellType(f.returnKind, f.returnStruct)));
        }
    }

    // Read the parameters that no argument mentions out of the bounds of the ones that do.
    // `I: Iter<T>` with I = Range: Range implements `Iter<long>`, so the bound's argument list
    // and the impl's line up and T is whatever sits where T was written. Only bounds whose own
    // subject is already bound can say anything, so this runs after the arguments are matched.
    inferThroughBounds &self inout a:Ast inout bind:HashMap<str, TypeRef> t:GTemplate f:FnNode -> void {
        for b in 0..f.boundCount {
            mb: MethodBound = gReg.boundAt(f.firstBound + b);
            if (mb.trait.argCount == 0 || mb.param >= t.paramCount) { continue; }
            subject: Option<TypeRef> = bind.find(nameOf(gReg.gParamAt(t, mb.param)));
            sub: TypeRef = TypeRef { base: Lit.Void, name: NO_SYM };
            match subject { Some(v) { sub = v; } None { continue; } }
            // A callable bound (`F: Fn(sink U, &T) -> U`) is answered by the signature of the
            // callable F turned out to be: a fn value's or a closure's. That is a fact about the
            // call, so it speaks before a literal: `fold(xs, 0, &addLL)` with `addLL` over `long`s
            // makes U a `long` (otherwise the `0` would make it an `int`, and the body would store
            // a `long` in it).
            if (isCoreTraitName(lastComponentOf(nameOf(mb.trait.name))) && strStartsWith(lastComponentOf(nameOf(mb.trait.name)), "Fn")) {
                self.bindFromCallable(a, bind, mb.trait, sub);
                continue;
            }
            if (sub.base != Lit.Struct) { continue; }
            // The impl of that trait the concrete subject has, and its arguments beside the
            // bound's: a type variable in the bound is answered by what stands opposite it.
            for i in 0..gReg.implCount() {
                im: TraitImplDef = gReg.implAt(i);
                if (im.structName != sub.name || im.trait.name != mb.trait.name) { continue; }
                if (im.trait.argCount != mb.trait.argCount) { continue; }
                for k in 0..mb.trait.argCount {
                    want: TypeRef = gReg.traitArgAt(mb.trait, k);
                    have: TypeRef = gReg.traitArgAt(im.trait, k);
                    if (want.base == Lit.TypeVar && !bind.has(nameOf(want.name))) {
                        bind.put(nameOf(want.name), have);
                    }
                }
            }
        }
    }

    // The parameters and result of the callable `sub` against a callable bound's arguments (the
    // parameters, then the result), binding each type variable the bound names there.
    bindFromCallable &self inout a:Ast inout bind:HashMap<str, TypeRef> tr:TraitRef sub:TypeRef -> void {
        n: long = tr.argCount - 1;
        if (sub.base == Lit.Fn) {
            gi: long = gFnSigs.find(sub.name);
            if (gi < 0) { return; }
            have: FnSig = gFnSigs.sigAt(gi);
            if (have.paramCount != n) { return; }
            for k in 0..n { self.bindPart(bind, gReg.traitArgAt(tr, k), fnParamType(gFnSigs.paramAt(have, k))); }
            self.bindPart(bind, gReg.traitArgAt(tr, n), have.ret);
            return;
        }
        if (sub.base != Lit.Struct || sub.name == NO_SYM) { return; }
        hit: Option<long> = self.fnAt.find(nameOf(methodSymbol(sub.name, intern("call"))));
        at: long = -1;
        match hit { Some(i) { at = i; } None { return; } }
        cf: FnNode = a.fns.get(at);
        if (cf.argCount != n + 1) { return; }                       // the closure's own state first
        for k in 0..n {
            pd: VarDeclNode = a.paramAt(cf, k + 1);
            self.bindPart(bind, gReg.traitArgAt(tr, k), TypeRef { base: pd.kind, name: pd.structName });
        }
        self.bindPart(bind, gReg.traitArgAt(tr, n), TypeRef { base: cf.returnKind, name: cf.returnStruct });
    }

    // What an argument's type actually is. An `inout` parameter is passed `&v`, and the borrow
    // itself is an address: what the parameter is being matched against is the value under it.
    lentValue &self inout a:Ast id:NodeId -> Expr {
        e: Expr = a.expr(id);
        if (e.op != Op.AddressOf) { return e; }
        // `&name` of a function is a value in its own right (a function pointer) not a lend of
        // something. Unwrapping it would match a parameter against the function's name instead of
        // against its type.
        if (self.addressedFn(a, id) != NO_SYM) { return e; }
        pl: Payload = e.payload;
        match pl { Sub(inner) { return a.expr(inner); } _ { } }
        return e;
    }

    // One parameter against one argument. A type parameter may stand alone or under a pointer,
    // a slice or a borrow; in each case what binds it is the matching part of the argument.
    //
    // `weak` says the argument was a bare integer literal, whose type is a default rather than a
    // fact: it fills a parameter nothing else reached and never overrides one already bound.
    bindParam &self inout bind:HashMap<str, TypeRef> p:VarDeclNode arg:Expr weak:bool -> void {
        if (p.kind == Lit.TypeVar) {
            if (weak && bind.has(nameOf(p.structName))) { return; }
            got: Lit = arg.kind;
            // A lent parameter (`inout t:T`) is passed as a borrow at every call site, so the
            // argument arrives as a ref whether it was written `&v` or came back from an `at()`
            // that already returned one. The borrow is the lend, not the type: T is what is
            // behind it, or `take(outer.at(0))` would bind `T = &Vec` and no bound on T could
            // ever be met. Elsewhere the borrow form is deliberately kept (an `Iter<&T>` really
            // does name the borrow), which is why this is decided here, where the parameter's
            // convention is in hand, and not wherever two types are matched.
            if (p.conv == Conv.Inout && got == Lit.Ref) { got = Lit.Struct; }
            bind.put(nameOf(p.structName), TypeRef { base: got, name: arg.structName });
            return;
        }
        // `*T` and `[T]` carry their element as a mangled name, so the argument's does too and
        // binding is a name-for-name match.
        if (p.kind == Lit.Ptr || p.kind == Lit.Slice) {
            if (arg.kind == p.kind && arg.structName != NO_SYM && p.structName != NO_SYM) {
                bind.put(nameOf(p.structName), typeRefNamed(nameOf(arg.structName)));
            }
            return;
        }
        // `f: fn(T) -> U` given `&dbl`. Both sides are keys into the signature table, so this is
        // a walk down two signatures: the results against each other and then each parameter
        // against its opposite number, and wherever the pattern has a type variable the argument
        // in that place is what it stands for. That is where `U` comes from (the type a mapping
        // function decides and nothing else in the call mentions), and also `T` when only the
        // callback names it.
        if (p.kind == Lit.Fn) {
            if (arg.kind != Lit.Fn) { return; }
            pi: long = gFnSigs.find(p.structName);
            gi: long = gFnSigs.find(arg.structName);
            if (pi < 0 || gi < 0) { return; }
            want: FnSig = gFnSigs.sigAt(pi);
            have: FnSig = gFnSigs.sigAt(gi);
            self.bindPart(bind, want.ret, have.ret);
            k: long = 0;
            while (k < want.paramCount && k < have.paramCount) {
                self.bindPart(bind, fnParamType(gFnSigs.paramAt(want, k)),
                                    fnParamType(gFnSigs.paramAt(have, k)));
                k = k + 1;
            }
            return;
        }
        if (p.kind == Lit.Struct || p.kind == Lit.Ref) {
            if (p.structName == NO_SYM || arg.structName == NO_SYM) { return; }
            // `&T` names the parameter itself; `Vec<T>` (`inout` or not) names an instance
            // whose arguments are still parameters, and T is found by matching the two
            // instantiations against each other.
            if (gReg.findRequestSym(p.structName) < 0 && !isTupleName(p.structName)) {
                bind.put(nameOf(p.structName), TypeRef { base: Lit.Struct, name: arg.structName });
                return;
            }
            self.bindInstance(bind, p.structName, arg.structName);
        }
    }

    // A parameter written as an instance of another template (`Vec<T>`, `Option<K>`) against the
    // instance actually passed. Both were recorded as requests when they were parsed, so this is
    // a walk down two argument lists: wherever the pattern has a type variable, the argument in
    // that place is what it stands for. Recurses, so `Vec<Option<T>>` binds T as well.
    bindInstance &self inout bind:HashMap<str, TypeRef> pat:Sym got:Sym -> void {
        // `(A, B)` against `(long, P)`: a tuple is named by its elements, so the walk is down
        // the two element lists, as it is down two instances' arguments.
        if (isTupleName(pat) && isTupleName(got)) {
            pe: Vec<TypeRef> = tupleElems(pat);
            ge: Vec<TypeRef> = tupleElems(got);
            if (pe.len() != ge.len()) { return; }
            for j in 0..pe.len() {
                pt: TypeRef = pe.get(j);
                gt: TypeRef = ge.get(j);
                if (pt.base == Lit.TypeVar) { bind.put(nameOf(pt.name), gt); }
                else if (pt.base == Lit.Struct && gt.base == Lit.Struct) { self.bindInstance(bind, pt.name, gt.name); }
            }
            return;
        }
        pi: long = gReg.findRequestSym(pat);
        gi: long = gReg.findRequestSym(got);
        if (pi < 0 || gi < 0) { return; }
        pr: GRequest = gReg.requestAt(pi);
        gr: GRequest = gReg.requestAt(gi);
        if (pr.base != gr.base || pr.argCount != gr.argCount) { return; }
        for k in 0..pr.argCount {
            pa: TypeRef = gReg.gArgAt(pr, k);
            ga: TypeRef = gReg.gArgAt(gr, k);
            if (pa.base == Lit.TypeVar) { bind.put(nameOf(pa.name), ga); }
            else if (pa.base == Lit.Struct && ga.base == Lit.Struct) {
                self.bindInstance(bind, pa.name, ga.name);
            }
        }
    }

    // One position of a signature against the same position of another. A bare type variable
    // takes what stands opposite it, and only when nothing else has already said: a callback's
    // signature is the last place to learn a type parameter from, never the place to overrule
    // one an argument already pinned. Two instances recurse, so `fn(Vec<T>)->void` given a
    // `fn(Vec<long>)->void` learns T as well.
    bindPart &self inout bind:HashMap<str, TypeRef> want:TypeRef have:TypeRef -> void {
        if (want.base == Lit.TypeVar) {
            if (want.name == NO_SYM || bind.has(nameOf(want.name))) { return; }
            if (have.base == Lit.TypeVar || have.base == Lit.Void) { return; }
            bind.put(nameOf(want.name), have);
            return;
        }
        if (want.base == Lit.Struct && have.base == Lit.Struct) {
            self.bindInstance(bind, want.name, have.name);
        }
    }

    // The same boxing an ordinary call gets, for a static one, whose parameters start at 0
    // because there is no receiver in front of them.
    boxTraitArgsStatic &self inout a:Ast cn:CallNode fn:Sym -> void {
        hit: Option<long> = self.fnAt.find(nameOf(fn));
        at: long = -1;
        match hit { Some(i) { at = i; } None { return; } }
        f: FnNode = a.fns.get(at);
        for k in 0..cn.argCount {
            if (k < f.argCount) {
                pd: VarDeclNode = a.paramAt(f, k);
                arg: NodeId = a.argAt(cn, k);
                if (pd.kind == Lit.TraitObj && isConcreteForTrait(a.expr(arg))) {
                    self.aimTraitObj(a, a.expr(arg).structName, pd.structName);
                    a.args.set(cn.firstArg + k, a.leafOf(Op.MakeTraitObj, Payload.Sub(arg),
                                                         Lit.TraitObj, pd.structName));
                }
            }
        }
    }

    // An expression checked where a value of type `want` is stored: a template literal is aimed
    // at it (below), and a call whose callee is generic may read its type parameters from it.
    // A macro call is expanded first, since what it produces is what gets aimed.
    //
    // `Option.Some(v)` names the template, because a constructor cannot know which instance it
    // is building: `Some(3)` could be an `Option<long>` or an `Option<int>`. The type the value
    // is being used as settles it, which is why this is done where that type is known: a
    // declaration's annotation, an assignment's target, a return's declared type.
    checkAimed &self inout a:Ast id:NodeId want:Sym -> VarType {
        if (id == NO_NODE) { return varType(Lit.Void, NO_SYM); }
        if (a.expr(id).op == Op.MacroCall) { self.spliceMacroCall(a, id); }
        self.resolveTemplateLit(a, id, want);
        if (want != NO_SYM && (a.expr(id).op == Op.FunctionCall || a.expr(id).op == Op.MethodCall)) { self.expectType = want; }
        t: VarType = self.checkExpr(a, id);
        self.expectType = NO_SYM;
        return t;
    }

    resolveTemplateLit &self inout a:Ast id:NodeId want:Sym -> void {
        if (id == NO_NODE || want == NO_SYM) { return; }
        e: Expr = a.expr(id);
        // A call passes the target through to its arguments:
        // `m: Option<long> = mapOption(Option.None, &dbl)` names no instance anywhere, and the
        // declaration is the only thing that says which. Only an argument of the same template is
        // aimed; the call's own parameters decide anything else.
        if (e.op == Op.FunctionCall || e.op == Op.MethodCall) {
            p2: Payload = e.payload;
            c: long = -1;
            match p2 { Call(v) { c = v; } _ { return; } }
            cn: CallNode = a.calls.get(c);
            for k in 0..cn.argCount {
                self.aimSameTemplate(a, a.argAt(cn, k), want);
            }
            return;
        }
        if (e.op == Op.TupleLit) { self.aimTupleLit(a, id, want); return; }
        if (e.op != Op.StructLit) { return; }
        p: Payload = e.payload;
        at: long = -1;
        match p { Lit(l) { at = l; } _ { return; } }
        n: LitNode = a.lits.get(at);
        if (gReg.findTemplateSym(n.typeName) < 0 && !self.aimSelfLit(at, n.typeName, want)) { return; }   // already an instance
        if (gReg.findStructSym(want) < 0) { return; }           // not stamped: nothing to aim at
        n.typeName = want;
        a.lits.set(at, n);
        e.kind = Lit.Struct;
        e.structName = want;
        a.exprs.set(id, e);
    }

    // `Pair { a: self.b, b: self.a }` in `methods Pair<A, B>`, returned from `-> Pair<B, A>`: the
    // clone typed the bare template name as its own instance (`gSelfLits`), and the destination
    // is another instance of the same template, which is the one meant.
    aimSelfLit &self at:long have:Sym want:Sym -> bool {
        if (want == NO_SYM || want == have || !gSelfLits.has(at)) { return false; }
        hr: long = gReg.findRequestSym(have);
        wr: long = gReg.findRequestSym(want);
        return hr >= 0 && wr >= 0 && gReg.requestAt(hr).base == gReg.requestAt(wr).base;
    }

    // `(a, b)` names nothing, and its elements' own types are not enough to say what it is:
    // `(65 as char, n * 2, 7)` returned from a `-> (char, long, int)` is that tuple, not the one
    // its three expressions happen to compute. So the type it is being used as settles it, and
    // once aimed it is an ordinary struct literal over the registered tuple's positional fields,
    // which is what lets the rest of the compiler stay ignorant of tuples.
    aimTupleLit &self inout a:Ast id:NodeId want:Sym -> void {
        if (!isTupleName(want)) { return; }
        si: long = gReg.findStructSym(want);
        if (si < 0) { return; }
        e: Expr = a.expr(id);
        p: Payload = e.payload;
        at: long = -1;
        match p { Lit(l) { at = l; } _ { return; } }
        n: LitNode = a.lits.get(at);
        d: StructDef = gReg.structDef(si);
        if (n.initCount != d.fieldCount) {
            failStr(format("mismatched types: expected a {}-element tuple, found a {}-element tuple",
                           d.fieldCount, n.initCount));
        }
        for k in 0..n.initCount {
            iv: InitNode = a.inits.get(n.firstInit + k);
            a.inits.set(n.firstInit + k,
                        InitNode { name: gReg.fieldAt(d, k).name, value: iv.value });
        }
        n.typeName = want;
        a.lits.set(at, n);
        e.op = Op.StructLit;
        e.kind = Lit.Struct;
        e.structName = want;
        a.exprs.set(id, e);
    }

    // `(a, b)` where nothing says which tuple it is (`x := ...` has no annotation to read; an
    // argument to a generic parameter; a value compared or matched): the tuple of what its
    // elements are, registered now if no declaration named it. Its elements are already typed.
    tupleOfElems &self inout a:Ast id:NodeId l:long -> VarType {
        n: LitNode = a.lits.get(l);
        elems: Vec<TypeRef>;
        for k in 0..n.initCount {
            v: Expr = a.expr(a.inits.get(n.firstInit + k).value);
            if (v.kind == Lit.Void) { failStr(stringOf("a tuple element has no value")); }
            // A borrow read out of a place is the value it lends, copied or moved by the store.
            kind: Lit = v.kind;
            if (kind == Lit.Ref) { kind = Lit.Struct; }
            elems.push(TypeRef { base: kind, name: v.structName });
        }
        want: Sym = registerTuple(elems);
        self.aimTupleLit(a, id, want);
        return varType(Lit.Struct, want);
    }

    // Aim an un-aimed template literal at `want`, but only when the two name the same template:
    // `Option.None` where an `Option<long>` is wanted is that one, and a `Result.Ok` there is not.
    aimSameTemplate &self inout a:Ast id:NodeId want:Sym -> void {
        if (id == NO_NODE) { return; }
        e: Expr = a.expr(id);
        if (e.op != Op.StructLit) { return; }
        p: Payload = e.payload;
        at: long = -1;
        match p { Lit(l) { at = l; } _ { return; } }
        base: Sym = a.lits.get(at).typeName;
        if (gReg.findTemplateSym(base) < 0) { return; }      // already an instance
        r: long = gReg.findRequestSym(want);
        if (r < 0 || gReg.requestAt(r).base != base) { return; }  // a different template
        self.resolveTemplateLit(a, id, want);
    }

    // Each argument of a call against the parameter it lands in: the count (`checkArity`), two
    // structs by name, and everything else by `typeFits`. A fn-typed argument against a fn-typed
    // parameter is also asked the one question a fn type exists to answer: `fn(Res)` lends its
    // argument and `fn(sink Res)` takes it, so a callee of one shape cannot stand in a slot of the
    // other. Whichever way round, one end would release what the other already released.
    checkFnArgs &self inout a:Ast cn:CallNode fn:Sym base:long -> void {
        hit: Option<long> = self.fnAt.find(nameOf(fn));
        at: long = -1;
        match hit { Some(i) { at = i; } None { return; } }
        f: FnNode = a.fns.get(at);
        self.checkArity(a, cn, f, fn, base);
        for k in 0..cn.argCount {
            if (base + k < f.argCount) {
                p: VarDeclNode = a.paramAt(f, base + k);
                got: Expr = a.expr(a.argAt(cn, k));
                if (p.kind == Lit.Struct && got.kind == Lit.Struct && !p.isVariadic
                    && p.structName != NO_SYM && got.structName != NO_SYM && p.structName != got.structName) {
                    if (self.readsTryLocal(a, a.argAt(cn, k))) {
                        self.refuseTryResidual(varType(got.kind, got.structName), varType(p.kind, p.structName));
                    }
                    failStr(format("mismatched types: expected `{}`, found `{}`\nnote: parameter `{}` of `{}` has type `{}`",
                                   nameOf(p.structName), nameOf(got.structName), nameOf(p.name), nameOf(fn), nameOf(p.structName)));
                }
                if (p.kind == Lit.Fn && got.kind == Lit.Fn && !p.isVariadic
                    && fnSigsClashOnOwnership(got.structName, p.structName)) {
                    failStr(format("mismatched types: expected `{}`, found `{}`\nnote: parameter `{}` of `{}` has type `{}`\nnote: a fn type lends a struct argument unless it says `sink`, and the function pointed to must do the same",
                                   nameOf(p.structName), nameOf(got.structName), nameOf(p.name), nameOf(fn),
                                   nameOf(p.structName)));
                }
                // A variadic parameter is a run of arguments of its element type, and binding
                // that element is `instantiate`'s job; nothing here has one type to hold them to.
                //
                // Against the lent value, not the borrow: an `inout` parameter is passed `&v`,
                // and the address is not what the parameter is being matched against.
                if (self.adoptFloat(a, a.argAt(cn, k), p.kind)) { }
                if (self.adoptWide(a, a.argAt(cn, k), p.kind)) { }
                val: Expr = self.lentValue(a, a.argAt(cn, k));
                vk: Lit = val.kind;
                vn: Sym = val.structName;
                // An `inout` scalar is held to its type where the lend is (`holdScalarLends`), and
                // a plain value there is refused once conventions are settled (`enforceCallSite`).
                inoutScalar: bool = p.kind == Lit.Ref && isInoutScalarName(p.structName);
                if (!p.isVariadic && !inoutScalar
                    && !typeFits(p.kind, p.structName, vk, vn,
                                 self.weakArg(a, a.argAt(cn, k)))) {
                    if (self.readsTryLocal(a, a.argAt(cn, k))) {
                        self.refuseTryResidual(varType(vk, vn), varType(p.kind, p.structName));
                    }
                    failStr(format("mismatched types: expected `{}`, found `{}`\nnote: parameter `{}` of `{}` has type `{}`",
                                   self.spellType(p.kind, p.structName), self.spellType(vk, vn),
                                   nameOf(p.name), nameOf(fn), self.spellType(p.kind, p.structName)));
                }
            }
            self.checkAnyArg(a, cn, f, fn, base, k);
        }
    }

    // An argument that lands in a `...any` run. `any` is a 24-byte box with a tag, and `boxAny`
    // in the lowerer knows exactly six shapes to build one from; a value of any other type would
    // have its first word stored as if it were the whole thing. A `[u8]` shows why that matters:
    // sixteen bytes would be written as eight, and the formatter would read a length as a
    // pointer.
    checkAnyArg &self inout a:Ast cn:CallNode f:FnNode fn:Sym base:long k:long -> void {
        if (f.argCount == 0) { return; }
        last: VarDeclNode = a.paramAt(f, f.argCount - 1);
        if (!last.isVariadic || last.elemKind != Lit.Any) { return; }
        // Only the arguments that fall into the run, which begins where the fixed ones end.
        if (base + k < f.argCount - 1) { return; }
        // `E.V` of a backed enum is an integer literal that remembers E (`Parser.enumConst`). In
        // a `...any` run it is the value of E it names, so it is boxed through E's `Display`, as a
        // local of type E is: the literal becomes `lit as E`.
        arg: NodeId = a.argAt(cn, k);
        le: Expr = a.expr(arg);
        if (le.op == Op.Literal && isInteger(le.kind) && namedScalar(Lit.Struct, le.structName)
            && gReg.structImplements(nameOf(le.structName), intern("Display"))) {
            lit: NodeId = a.addExpr(le);
            a.setExpr(arg, Expr { op: Op.Cast, left: NO_NODE, right: NO_NODE, kind: Lit.Struct,
                                  structName: le.structName, isParen: false, payload: Payload.Sub(lit) });
        }
        v: Expr = self.lentValue(a, arg);
        if (boxableAsAny(v.kind, v.structName)) { return; }
        failStr(format("cannot pass `{}` as `any` in argument {} of `{}`\nnote: an `any` holds an integer, a `str`, a pointer, or a value whose type implements `Display`",
                       self.spellType(v.kind, v.structName), base + k, nameOf(fn)));
    }

    // How many arguments the callee declared, against how many the call gives. A variadic last
    // parameter takes the rest, zero of them included, so it sets a floor rather than a count.
    //
    // Without this, a call with too few arguments would read whatever the argument register
    // happened to hold, and one with too many would leave the extras evaluated and dropped.
    checkArity &self inout a:Ast cn:CallNode f:FnNode fn:Sym base:long -> void {
        want: long = f.argCount - base;
        if (want < 0) { return; }
        variadic: bool = want > 0 && a.paramAt(f, f.argCount - 1).isVariadic;
        if (variadic) {
            if (cn.argCount >= want - 1) { return; }
            failStr(format("too few arguments to `{}`: expected at least {}, found {}",
                           nameOf(fn), want - 1, cn.argCount));
        }
        if (cn.argCount == want) { return; }
        which: str = "too many";
        if (cn.argCount < want) { which = "too few"; }
        failStr(format("{} arguments to `{}`: expected {}, found {}",
                       which, nameOf(fn), want, cn.argCount));
    }

    // A type as a diagnostic should name it: a struct or a slice by its own name, a scalar by
    // its spelling. `typeName` alone answers "struct" for every struct there is.
    spellType &self k:Lit n:Sym -> str {
        if (n == NO_SYM) { return typeName(k); }
        if (k == Lit.Struct || k == Lit.TraitObj || k == Lit.Fn) { return nameOf(n); }   // a fn type by its key, `fn(Res)->long`
        if (k == Lit.Ref) { return keepString(format("&{}", nameOf(n))); }
        if (k == Lit.Slice) { return keepString(format("[{}]", nameOf(n))); }
        if (k == Lit.Ptr) { return keepString(format("*{}", nameOf(n))); }
        if (k == Lit.Len) { return keepString(format("the length {}", nameOf(n))); }
        return typeName(k);
    }

    // A concrete value handed to a trait-typed parameter becomes a trait object there: the
    // argument is wrapped in a `MakeTraitObj`, which lowering turns into the {data, vtable} pair.
    // This is done here rather than in the parser because it takes the callee's signature to know
    // that the parameter is a trait at all.
    boxTraitArgs &self inout a:Ast cn:CallNode fn:Sym -> void {
        hit: Option<long> = self.fnAt.find(nameOf(fn));
        at: long = -1;
        match hit { Some(i) { at = i; } None { return; } }
        f: FnNode = a.fns.get(at);
        // A method call passes its receiver as parameter 0, so the arguments start one later.
        base: long = 0;
        if (cn.receiver != NO_NODE) { base = 1; }
        for k in 0..cn.argCount {
            if (base + k < f.argCount) {
                p: VarDeclNode = a.paramAt(f, base + k);
                arg: NodeId = a.argAt(cn, k);
                got: Expr = a.expr(arg);
                if (p.kind == Lit.TraitObj && isConcreteForTrait(got)) {
                    self.aimTraitObj(a, got.structName, p.structName);
                    if (!self.mayImplement(got.structName, p.structName)) {
                        failStr(format("`{}` does not implement `{}`\nnote: argument {} of `{}` is passed as a trait object of `{}`",
                                       self.spellType(Lit.Struct, got.structName), self.spellType(Lit.TraitObj, p.structName),
                                       base + k, nameOf(fn), self.spellType(Lit.TraitObj, p.structName)));
                    }
                    a.args.set(cn.firstArg + k, a.leafOf(Op.MakeTraitObj, Payload.Sub(arg),
                                                         Lit.TraitObj, p.structName));
                }
            }
        }
    }

    // `x.m()` where `x`'s type implements a trait the module being checked owns (`trait Ord`
    // declared without `pub` here) and that trait has `m`: that implementation's method, whose
    // name carries the trait (`implFnName`). Several (two of this module's traits with one method
    // name, or one trait at several arguments) are told apart by the first argument as `overload`
    // does, and refused when it does not settle them. NO_SYM when there is none.
    ownTraitMethod &self inout a:Ast owner:Sym method:Sym cn:CallNode -> Sym {
        if (gReg.ownedTraits.len() == 0 || self.currentModule == NO_SYM) { return NO_SYM; }
        mod: str = nameOf(self.currentModule);
        found: Sym = NO_SYM;
        fits: Sym = NO_SYM;
        count: long = 0;
        arg: NodeId = NO_NODE;
        if (cn.argCount > 0) { arg = a.argAt(cn, 0); }
        // By index: naming a method may register what its trait's arguments mention, which is
        // writing `gReg`, so the list is read afresh each time rather than walked in place.
        for ti in 0..gReg.ownedTraits.len() {
            t: Sym = gReg.ownedTraits.get(ti);
            tn: str = nameOf(t);
            if (tn.len <= mod.len + 2 || strSlice(tn, 0, mod.len) != mod || charAt(tn, mod.len) != ':') { continue; }
            if (lastComponentOf(tn).len != tn.len - mod.len - 2) { continue; }
            i: long = gReg.firstImplOf(owner, t);
            while (i >= 0) {
                cand: Sym = implMethodName(gReg.implAt(i), method);
                if (self.fnNames.has(nameOf(cand))) {
                    count = count + 1;
                    found = cand;
                    if (arg != NO_NODE && fits == NO_SYM && self.paramFits(a, cand, a.expr(arg))) { fits = cand; }
                }
                i = gReg.nextImplOf(i);
            }
        }
        if (count <= 1) { return found; }
        if (fits != NO_SYM) { return fits; }
        failStr(format("`{}.{}` is ambiguous\nnote: more than one of this file's traits gives `{}` a method `{}`",
                       self.spellType(Lit.Struct, owner), nameOf(method), self.spellType(Lit.Struct, owner),
                       nameOf(method)));
        return found;
    }

    // `@(e)` in a quote, which the quoter wrote as `e.$splice()`. A Node is cloned, so one tree may
    // be spliced in several places; an integer, a `bool` or a `char` becomes `Node.Int(e)` and a
    // `str` `Node.Str(e)`, the literal the macro's tree then holds. What `e` is is read without
    // typing it, so nothing is typed twice: a variable, a field of one, a literal. Anything else
    // is typed in place and must be a Node.
    checkSplice &self inout a:Ast id:NodeId c:long cn:CallNode -> VarType {
        nodeSym: Sym = intern("ast::Node");
        t: VarType = self.placeType(a, cn.receiver);
        variant: str = "";
        if (isInteger(t.kind) || t.kind == Lit.Bool || t.kind == Lit.Char) { variant = "Int"; }
        if (t.kind == Lit.Str) { variant = "Str"; }
        if (variant.len > 0) {
            qt: Quoter = Quoter { node: nodeSym, binOp: intern("ast::BinOp"), unOp: intern("ast::UnOp") };
            one: Vec<NodeId>;
            one.push(cn.receiver);
            built: NodeId = qt.qVariant(a, variant, one);
            a.setExpr(id, a.expr(built));
            return self.checkExpr(a, id);
        }
        a.calls.set(c, CallNode { name: intern("clone"), receiver: cn.receiver, firstArg: cn.firstArg,
                                  argCount: cn.argCount, slot: cn.slot, callee: cn.callee, sigKey: cn.sigKey });
        got: VarType = self.checkExpr(a, id);
        if (got.kind != Lit.Struct || got.structName != nodeSym) {
            failStr(format("cannot splice a value of type `{}` with `@(...)`\nnote: `@(...)` in a quote splices a `Node`, or an integer, a `bool` or a `str` as a literal, and a value spliced as a literal is read from a variable or a field\nhelp: bind it to a local first",
                           self.spellType(got.kind, got.structName)));
        }
        return got;
    }

    // An expression's type where it can be read without typing it: a local, a field of one, a
    // literal. Void otherwise.
    placeType &self inout a:Ast id:NodeId -> VarType {
        none: VarType = varType(Lit.Void, NO_SYM);
        if (id == NO_NODE) { return none; }
        e: Expr = a.expr(id);
        if (e.op == Op.StringLit) { return varType(Lit.Str, NO_SYM); }
        if (e.op == Op.Literal) {
            match e.payload { Num(v) { return varType(e.kind, NO_SYM); } _ { } }
            return none;
        }
        if (e.op == Op.Lvalue) {
            match e.payload { Name(n) { return self.lookup(n); } _ { } }
            return none;
        }
        if (e.op != Op.FieldAccess) { return none; }
        fd: FieldNode = FieldNode { base: NO_NODE, name: NO_SYM };
        match e.payload { Field(f) { fd = a.fields.get(f); } _ { return none; } }
        b: VarType = self.placeType(a, fd.base);
        if ((b.kind != Lit.Struct && b.kind != Lit.Ref) || b.structName == NO_SYM) { return none; }
        si: long = gReg.findStructSym(b.structName);
        if (si < 0) { return none; }
        fi: long = gReg.findFieldSym(gReg.structDef(si), fd.name);
        if (fi < 0) { return none; }
        f: FieldDef = gReg.fieldAt(gReg.structDef(si), fi);
        if (f.isArray) { return none; }
        return varType(f.kind, f.structName);
    }

    // The receiver of `Show.text(x)` when it names a trait (this module's own, or a flat one) and
    // nothing else: no variable, no type of that spelling. NO_SYM otherwise.
    traitNamed &self inout a:Ast recv:NodeId -> Sym {
        if (recv == NO_NODE) { return NO_SYM; }
        e: Expr = a.expr(recv);
        if (e.op != Op.Lvalue) { return NO_SYM; }
        n: Sym = NO_SYM;
        match e.payload { Name(x) { n = x; } _ { return NO_SYM; } }
        if (self.lookup(n).kind != Lit.Void || gReg.traits.len() == 0) { return NO_SYM; }      // a variable, as most receivers are
        q: Sym = NO_SYM;
        // This file's own trait first, as a type of its own would be.
        if (self.currentModule != NO_SYM && !gReg.ownedTraits.isEmpty()) {
            own: Sym = qualifiedSym(self.currentModule, n);
            if (gReg.findTraitSym(own) >= 0) { q = own; }
        }
        if (q == NO_SYM && gReg.findTraitSym(n) >= 0) { q = n; }
        if (q == NO_SYM || gReg.hasStructSym(n) || gReg.findEnumSym(n) >= 0) { return NO_SYM; }
        return q;
    }

    // Whether trait `tr` declares `m` without a receiver (a constructor: `new -> Self`). A trait
    // that declares no `m` at all is left to `traitMethodFor` to refuse.
    traitMethodIsStatic &self tr:Sym m:Sym -> bool {
        ti: long = gReg.findTraitSym(tr);
        if (ti < 0) { return false; }
        slot: long = gReg.methodSlot(gReg.traitDef(ti), nameOf(m));
        if (slot < 0) { return false; }
        return gReg.traitMethodAt(gReg.traitDef(ti), slot).isStatic;
    }

    // `Show.text(x)`: Show's method for x's type. A core trait's is the plain method (core traits
    // never share a name with another's: `Registry.flatCarries`), so that is left to the ordinary
    // lookup, derives and all. NO_SYM leaves the target as it was.
    traitMethodFor &self inout a:Ast owner:Sym tr:Sym cn:CallNode -> Sym {
        ti: long = gReg.findTraitSym(tr);
        slot: long = gReg.methodSlot(gReg.traitDef(ti), nameOf(cn.name));
        if (slot < 0) {
            failStr(format("no method `{}` in trait `{}`", nameOf(cn.name), lastComponentOf(nameOf(tr))));
        }
        // The argument that decides between implementations of a trait with arguments: a
        // method's first after the receiver (its parameter 1), a static method's first.
        param: long = 1;
        if (gReg.traitMethodAt(gReg.traitDef(ti), slot).isStatic) { param = 0; }
        if (isCoreTraitName(nameOf(tr))) { return NO_SYM; }
        i: long = gReg.firstImplOf(owner, tr);
        if (i < 0 && gReg.hasDerives()) {
            self.ensureImpl(a, owner, tr, 0);
            i = gReg.firstImplOf(owner, tr);
        }
        if (i < 0) {
            failStr(format("`{}` does not implement `{}`\nnote: `{}.{}(...)` calls that trait's method, so there is nothing to call",
                           self.spellType(Lit.Struct, owner), lastComponentOf(nameOf(tr)),
                           lastComponentOf(nameOf(tr)), nameOf(cn.name)));
        }
        // A trait with arguments may be implemented several times: the argument decides.
        arg: NodeId = NO_NODE;
        if (cn.argCount > 0) { arg = a.argAt(cn, 0); }
        found: Sym = NO_SYM;
        count: long = 0;
        while (i >= 0) {
            cand: Sym = implMethodName(gReg.implAt(i), cn.name);
            if (self.fnNames.has(nameOf(cand))) {
                count = count + 1;
                if (found == NO_SYM || (arg != NO_NODE && self.paramFitsAt(a, cand, a.expr(arg), param))) { found = cand; }
            }
            i = gReg.nextImplOf(i);
        }
        return found;
    }

    // `x.m()` on a type two flat traits each give an `m` (the second's carries its trait:
    // `Registry.flatCarries`): which one, or an error naming both, as Rust's "multiple applicable
    // items" does. A generic body stamped here may say, through the bound its receiver's type
    // parameter carries (`T: Show` makes `x.text()` Show's: `gCallHints`, from monomorphization).
    carriedAmbiguity &self inout a:Ast c:long owner:Sym m:Sym target:Sym isStatic:bool -> Sym {
        i: long = gReg.firstCarriedOf(owner);
        if (i < 0) { return target; }
        cands: Vec<Sym>;          // the methods
        traits: Vec<Sym>;         // and whose
        while (i >= 0) {
            im: TraitImplDef = gReg.implAt(i);
            cand: Sym = implMethodName(im, m);
            if (self.fnNames.has(nameOf(cand))) { cands.push(cand); traits.push(im.trait.name); }
            i = gReg.nextCarriedOf(i);
        }
        if (cands.len() == 0) { return target; }
        // The implementation that kept the plain name, if it has this method: named first, as it
        // was declared first.
        if (self.fnNames.has(nameOf(target))) {
            for k in 0..gReg.implCount() {
                im: TraitImplDef = gReg.implAt(k);
                if (im.structName != owner || im.carried || traitCarriesName(im.trait)) { continue; }
                if (implMethodName(im, m) == target) {
                    cands.insert(0, target);
                    traits.insert(0, im.trait.name);
                    break;
                }
            }
        }
        if (cands.len() == 1) { return cands.get(0); }
        hint: Option<long> = gCallHints.find(c);
        match hint {
            Some(h) {
                pick: Sym = NO_SYM;
                hits: long = 0;
                for k in 0..traits.len() {
                    j: long = h;
                    while (gHintTraits.get(j) != NO_SYM) {
                        if (gHintTraits.get(j) == traits.get(k)) { pick = cands.get(k); hits = hits + 1; break; }
                        j = j + 1;
                    }
                }
                if (hits == 1) { return pick; }
            }
            None { }
        }
        names: String;
        for k in 0..traits.len() {
            if (k > 0) { if (k + 1 == traits.len()) { names.pushStr("` and `"); } else { names.pushStr("`, `"); } }
            names.pushStr(lastComponentOf(nameOf(traits.get(k))));
        }
        // A static method is named by its trait with the type its result goes to.
        how: String = format("`{}.{}(x)`", lastComponentOf(nameOf(traits.get(0))), nameOf(m));
        if (isStatic) {
            how = format("`v: {} = {}.{}()`", self.spellType(Lit.Struct, owner),
                         lastComponentOf(nameOf(traits.get(0))), nameOf(m));
        }
        failStr(format("`{}.{}` is ambiguous\nnote: `{}` each give `{}` a method `{}`\nhelp: say which, as {}",
                       self.spellType(Lit.Struct, owner), nameOf(m), names, self.spellType(Lit.Struct, owner),
                       nameOf(m), how));
    }

    // `s.eq(other)` where `String` implements `Eq<str>` and `Eq<String>`. Each impl named its
    // method after its own instantiation, so the candidates are found through the impls, and the
    // one that fits is the one whose declared parameter is the type actually being passed. With a
    // single candidate the argument settles nothing, and it is taken as written.
    overload &self inout a:Ast owner:Sym method:Sym arg:NodeId -> Sym {
        only: Sym = NO_SYM;
        found: long = 0;
        i: long = 0;
        while (i < gReg.implCount()) {
            im: TraitImplDef = gReg.implAt(i);
            if (im.structName != owner || im.trait.argCount == 0) { i = i + 1; continue; }
            cand: Sym = methodSymbol(methodSymbol(owner, intern(gReg.traitMangled(im.trait))),
                                     method);
            if (self.fnNames.has(nameOf(cand))) {
                found = found + 1;
                only = cand;
                if (arg != NO_NODE && self.paramFits(a, cand, a.expr(arg))) { return cand; }
            }
            i = i + 1;
        }
        if (found == 1) { return only; }
        return NO_SYM;
    }

    // `owner.m(...)` with no plain static `m`: the one a parameterized trait's implementation for
    // `owner` gives (`owner_Trait_A_m`), or of several, the one whose first parameter is the first
    // argument's type. NO_SYM when there is none.
    staticOverload &self inout a:Ast owner:Sym cn:CallNode -> Sym {
        only: Sym = NO_SYM;
        found: long = 0;
        for i in 0..gReg.implCount() {
            im: TraitImplDef = gReg.implAt(i);
            if (im.structName != owner || im.trait.argCount == 0) { continue; }
            cand: Sym = methodSymbol(methodSymbol(owner, intern(gReg.traitMangled(im.trait))), cn.name);
            if (self.fnNodeOf(cand) < 0 && !self.fnNames.has(nameOf(cand))) { continue; }
            found = found + 1;
            only = cand;
            if (cn.argCount > 0 && self.paramFitsAt(a, cand, a.expr(a.argAt(cn, 0)), 0)) { return cand; }
        }
        if (found > 1) {
            failStr(format("`{}.{}` is ambiguous\nnote: `{}` has {} static methods `{}`, one per implementation of a parameterized trait, and the first argument does not say which",
                           self.spellType(Lit.Struct, owner), nameOf(cn.name), self.spellType(Lit.Struct, owner), found, nameOf(cn.name)));
        }
        return only;
    }

    // Whether a candidate's first argument (parameter 1, since the receiver is parameter 0)
    // is the type being passed.
    paramFits &self inout a:Ast fn:Sym arg:Expr -> bool { return self.paramFitsAt(a, fn, arg, 1); }
    paramFitsAt &self inout a:Ast fn:Sym arg:Expr k:long -> bool {
        hit: Option<long> = self.fnAt.find(nameOf(self.resolveFn(fn)));
        at: long = -1;
        match hit { Some(i) { at = i; } None { return false; } }
        f: FnNode = a.fns.get(at);
        if (f.argCount < k + 1) { return false; }
        p: VarDeclNode = a.paramAt(f, k);
        // A struct parameter and a borrow of one take the same argument; only the name decides.
        if (p.kind == Lit.Struct || p.kind == Lit.Ref) {
            return (arg.kind == Lit.Struct || arg.kind == Lit.Ref) && p.structName == arg.structName;
        }
        return p.kind == arg.kind;
    }

    // Whether a trait can be a vtable, and if not, why. Behind a trait object the receiver's
    // type is erased, and two shapes need it back: a method with no receiver has nothing to
    // dispatch on (there is no value to find the table from), and a method naming `Self` in its
    // parameters cannot say what that second operand is once the first one's type is gone.
    //
    // Both are still perfectly good bounds: `T: Default` and `T: Ord` resolve statically, where
    // the type is known. It is only the object form that cannot be built. The message says which
    // method is responsible, since that is what the author has to change.
    objectSafeProblem &self inout a:Ast trait:Sym -> str {
        if (trait == NO_SYM) { return ""; }
        at: long = gReg.findTraitSym(trait);
        if (at < 0) { return ""; }
        t: TraitDef = gReg.traitDef(at);
        for k in 0..t.methodCount {
            sig: TraitMethodSig = gReg.traitMethodAt(t, k);
            if (sig.isStatic) {
                return keepString(format("`{}` takes no receiver, so there is no value to find a table from",
                                         nameOf(sig.name)));
            }
            for i in 0..sig.paramCount {
                p: VarDeclNode = a.decls.get(a.params.get(sig.firstParam + i));
                if (p.structName != NO_SYM && nameOf(p.structName) == "Self") {
                    return keepString(format("`{}` takes a `Self` parameter, which names a type the object has erased",
                                             nameOf(sig.name)));
                }
            }
        }
        return "";
    }

    // A concrete value becoming a trait object, held to the trait being able to be one.
    requireObjectSafe &self inout a:Ast trait:Sym -> void {
        why: str = self.objectSafeProblem(a, trait);
        if (why.len == 0) { return; }
        failStr(format("the trait `{}` cannot be made into an object\nnote: {}\nhelp: use it as a bound, where the type is known",
                       nameOf(trait), why));
    }

    // The table a boxed value's vtable pointer names carries the trait instantiation, so boxing a
    // closure into `Fn(long) -> long` needs an impl registered under exactly that. A closure's own
    // is registered against the bare `FnN`, which is enough for a bound (a bound asks only for the
    // name), so this is where the precise one is added, and where a return type the body only
    // implied meets the one the annotation states.
    aimTraitObj &self inout a:Ast concrete:Sym trait:Sym -> void {
        if (concrete == NO_SYM || trait == NO_SYM) { return; }
        // A value becoming an object of a trait it has no implementation of yet: its vtable is
        // made of the implementation a derive writes, or a generic type's conditional one.
        if (gReg.hasDerives() && gReg.findTraitSym(trait) >= 0) { self.ensureImpl(a, concrete, trait, 0); }
        if (!self.fnNames.has(nameOf(methodName(concrete, intern("call"))))) { return; }
        tr: TraitRef = TraitRef { name: trait, firstArg: 0, argCount: 0 };
        if (gReg.implementsTrait(concrete, tr)) { return; }
        fns: Vec<Sym>;
        fns.push(methodName(concrete, intern("call")));
        gReg.addImpl(concrete, tr, fns);
    }

    // Whether `concrete` implements `trait`, or might yet: an instance whose template has an
    // implementation of it (a conditional one is stamped once its bounds are known to hold), or a
    // type not laid out yet. A value made into an object of a trait it does not implement would
    // otherwise reach the assembler as a vtable slot naming a method nobody defined
    // (`Mutex<BufWriter<Write>>` handed to a `Write` parameter).
    mayImplement &self concrete:Sym trait:Sym -> bool {
        // An instance (`Iter_long`) is implemented under its base trait with arguments
        // (`methods Range for Iter<long>`), and only that instantiation counts.
        tn: Sym = trait;
        inst: long = gReg.traitInstOf(trait);
        if (inst >= 0) {
            ref: TraitRef = gReg.traitInstRef(inst);
            if (gReg.implementsTrait(concrete, ref)) { return true; }
            tn = ref.name;
        }
        bare: Sym = intern(lastComponentOf(nameOf(tn)));
        if (inst < 0 && (gReg.structImplements(nameOf(concrete), tn) || gReg.structImplements(nameOf(concrete), bare))) { return true; }
        if (gReg.findStructSym(concrete) < 0 || isClosureStruct(concrete)) { return true; }
        r: long = gReg.findRequestSym(concrete);
        if (r < 0) { return false; }
        base: Sym = gReg.requestAt(r).base;
        for i in 0..gReg.implCount() {
            im: TraitImplDef = gReg.implAt(i);
            if (im.structName == base && (im.trait.name == tn || im.trait.name == bare)) { return true; }
        }
        return false;
    }

    // A value whose clone is itself: a scalar, a backed enum or distinct type, a `str` or slice
    // (a view), a raw or function pointer. Not a struct (its clone is derived or written), not a
    // borrow (that is the struct behind it), not a trait object.
    plainClone &self v:VarType -> bool {
        if (v.kind == Lit.Struct) { return namedScalar(Lit.Struct, v.structName); }
        if (v.kind == Lit.Ref || v.kind == Lit.TraitObj || v.kind == Lit.TypeVar || v.kind == Lit.Void) { return false; }
        return gReg.isCopy(v.kind, v.structName);
    }

    // Does a value of this type answer `call`? True for a closure struct, for a borrow of one,
    // and for an `Fn` trait object: the three shapes a callable value arrives in.
    callable &self v:VarType -> bool {
        if (v.structName == NO_SYM) { return false; }
        if (v.kind == Lit.TraitObj) {
            at: long = gReg.findTraitSym(v.structName);
            if (at < 0) { return false; }
            return gReg.methodSlot(gReg.traitDef(at), "call") >= 0;
        }
        if (v.kind != Lit.Struct && v.kind != Lit.Ref) { return false; }
        return self.fnNames.has(nameOf(methodSymbol(v.structName, intern("call"))));
    }

    // A field whose type answers `call`: a closure a struct was built around. A method of that
    // name wins, as it does for a fn-typed field.
    callableField &self owner:Sym name:Sym -> long {
        if (self.fnNames.has(nameOf(methodSymbol(owner, name)))) { return NOT_FOUND; }
        at: long = gReg.findStructSym(owner);
        if (at < 0) { return NOT_FOUND; }
        d: StructDef = gReg.structDef(at);
        k: long = gReg.findFieldSym(d, name);
        if (k < 0) { return NOT_FOUND; }
        f: FieldDef = gReg.fieldAt(d, k);
        if (!self.callable(varType(f.kind, f.structName))) { return NOT_FOUND; }
        return k;
    }

    // Which field of `owner` is a fn named `name`, or -1. A method wins over a field of the same
    // name: a method is what the dot usually means, and only the absence of one asks this.
    fnField &self owner:Sym name:Sym -> long {
        if (self.fnNames.has(nameOf(methodSymbol(owner, name)))) { return NOT_FOUND; }
        at: long = gReg.findStructSym(owner);
        if (at < 0) { return NOT_FOUND; }
        d: StructDef = gReg.structDef(at);
        k: long = gReg.findFieldSym(d, name);
        if (k < 0) { return NOT_FOUND; }
        if (gReg.fieldAt(d, k).kind != Lit.Fn) { return NOT_FOUND; }
        return k;
    }

    // The fn-type companion of `&name` when `name` is a function, or NO_SYM. The pointer's type
    // is the function's whole signature (its parameters with their declared conventions, and its
    // result) rebuilt and interned here, which is the same key `parseTypeRef` gives the matching
    // `fn(..) -> R` written out. So a `fn` variable and the address assigned to it agree, and a
    // `sink` written on the function keys a different pointer type from one written without.
    //
    // Declared, not inferred: inference has not run when an expression is typed. A function whose
    // convention inference later disagrees with the pointer it was taken through is caught by
    // `enforceFnRef`, once there is an answer to disagree with.
    addressedFn &self inout a:Ast id:NodeId -> Sym {
        p: Payload = a.expr(id).payload;
        inner: NodeId = NO_NODE;
        match p { Sub(v) { inner = v; } _ { return NO_SYM; } }
        if (inner == NO_NODE) { return NO_SYM; }
        e: Expr = a.expr(inner);
        if (e.op != Op.Lvalue) { return NO_SYM; }
        n: Sym = NO_SYM;
        q: Payload = e.payload;
        match q { Name(x) { n = x; } _ { return NO_SYM; } }
        if (self.lookup(n).kind != Lit.Void) { return NO_SYM; }   // a variable of that name wins
        fn: Sym = self.resolveFn(n);
        if (!self.fnNames.has(nameOf(fn))) { return NO_SYM; }
        // Written down where the back end will look for it: `&isOdd` has to become the address of
        // a label, and only a resolved, qualified name says which one.
        e.kind = Lit.Fn;
        e.payload = Payload.Name(fn);
        a.setExpr(inner, e);
        r: VarType = self.returnOf(fn);
        ps: Vec<FnParam>;
        at: long = self.fnNodeOf(fn);
        if (at >= 0) {
            fd: FnNode = a.fns.get(at);
            for k in 0..fd.argCount {
                pd: VarDeclNode = a.paramAt(fd, k);
                ps.push(FnParam { kind: pd.kind, name: pd.structName, conv: pd.conv });
            }
        }
        return gFnSigs.register(ps, TypeRef { base: r.kind, name: r.structName });
    }

    // A call through a trait object: the slot is written onto the call, and the answer is what
    // the trait says the method returns, since every implementation had to agree with it.
    checkDispatch &self inout a:Ast c:long cn:CallNode trait:Sym -> VarType {
        at: long = gReg.findTraitSym(trait);
        if (at < 0) { return varType(Lit.Void, NO_SYM); }
        t: TraitDef = gReg.traitDef(at);
        slot: long = gReg.methodSlot(t, nameOf(cn.name));
        if (slot < 0) {
            failStr(format("no method `{}` in trait `{}`", nameOf(cn.name), nameOf(trait)));
        }
        sig: TraitMethodSig = gReg.traitMethodAt(t, slot);
        // An `inout` scalar the trait's signature lends: `&n`, or a forwarded `inout` scalar
        // parameter, as at a direct call (`enforceCallSite`, which a dispatch never reaches).
        for k in 0..cn.argCount {
            if (k >= sig.paramCount) { break; }
            p: VarDeclNode = a.decls.get(a.params.get(sig.firstParam + k));
            arg: NodeId = a.argAt(cn, k);
            ae: Expr = a.expr(arg);
            if (p.conv != Conv.Inout || p.kind != Lit.Ref || !isInoutScalarName(p.structName)) { continue; }
            if (ae.op == Op.AddressOf) { self.holdLend(a, arg, p, cn.name, k); self.forgetScalarLend(arg); continue; }
            if (ae.op == Op.Deref && lentPlaceOf(a, arg) != NO_NODE) { a.setExpr(arg, a.expr(lentPlaceOf(a, arg))); continue; }
            failStr(format("parameter {} of `{}.{}` is an `inout` scalar, and this argument is not lent\nhelp: lend it with `&`", k, nameOf(trait), nameOf(cn.name)));
        }
        a.calls.set(c, CallNode { name: cn.name, receiver: cn.receiver,
                                  firstArg: cn.firstArg, argCount: cn.argCount, slot: slot,
                                  callee: NO_NODE, sigKey: NO_SYM });
        return varType(sig.returnKind, sig.returnName);
    }

    // `p.x`: the field's declared type. The base must be an aggregate that has it.
    //
    // Every kind of base is answered here, including the ones with no fields at all. A base the
    // checker typed and let through would reach the lowerer, where a fat pointer's word is chosen
    // by name (`.len` is the second word, and any other name the first) and a struct's offset is
    // looked up: `s.foo` on a `str` would read `.ptr`, and anything else would stop there with an
    // internal error instead of a message about the program.
    checkField &self inout a:Ast f:long -> VarType {
        fn: FieldNode = a.fields.get(f);
        base: VarType = self.checkExpr(a, fn.base);
        // A fixed array has no fields; its length is part of its type.
        if (base.isArray) {
            self.noField(fn.name, self.spellArrayOf(a, fn.base, base), "no fields\nhelp: an array's length is part of its type; a slice of it (`[..]`) has a `len`");
        }
        // `str` and a slice are fat pointers with two fields of their own, not entries in the
        // struct table: the address of the bytes, and how many there are.
        if (base.kind == Lit.Str || base.kind == Lit.Slice) {
            // `.len` is a plain long and safe; `.ptr` is the raw base address, and a raw address
            // is a raw address however it was obtained.
            if (nameOf(fn.name) == "ptr") {
                self.requireUnsafe("taking the raw base address of a `str` or a slice");
                return varType(Lit.Ptr, base.structName);
            }
            if (nameOf(fn.name) == "len") { return varType(Lit.Long, NO_SYM); }
            self.noField(fn.name, spellTypeRef(TypeRef { base: base.kind, name: base.structName }), "fields `ptr`, `len`");
        }
        // `p.f` dereferences `p`.
        if (base.kind == Lit.Ptr) {
            self.requireUnsafe("accessing a field through a raw pointer");
        }
        // A type parameter (a template's body is checked only once it is stamped) and a type the
        // checker could not work out (an error already reported, or a recovery) have nothing to
        // judge against. Everything else that is not a laid-out struct has no fields at all.
        if (base.kind == Lit.TypeVar || base.kind == Lit.Void) { return varType(Lit.Void, NO_SYM); }
        if (base.structName == NO_SYM) {
            if (!fieldless(base.kind)) { return varType(Lit.Void, NO_SYM); }
            self.noField(fn.name, stringOf(typeName(base.kind)), "no fields");
        }
        at: long = gReg.findStructSym(base.structName);
        if (at < 0) {
            // Named, but not a struct: a trait object, an enum or a distinct type, a pointer to a
            // scalar, a fn type. A struct named here and not laid out yet is a stamping round
            // away from having its fields, and is left to that round.
            if (!self.namesFieldless(base)) { return varType(Lit.Void, NO_SYM); }
            if (base.kind == Lit.TraitObj) {
                tn: String = spellTypeRef(TypeRef { base: base.kind, name: base.structName });
                self.noField(fn.name, tn, "no fields\nhelp: a trait object is used through its methods");
            }
            self.noField(fn.name, spellTypeRef(TypeRef { base: base.kind, name: base.structName }), "no fields");
        }
        d: StructDef = gReg.structDef(at);
        k: long = gReg.findFieldSym(d, fn.name);
        // The struct is registered and has no such member. Typed `void`, `p.nosuch` would reach
        // the lowerer, where `fieldOffset` has no answer either and gives 0, a valid offset (the
        // first field's), so the read would come back as some other member's value.
        if (k < 0) {
            self.noField(fn.name, spellTypeName(nameOf(base.structName)), fieldNamesOf(d));
        }
        fd: FieldDef = gReg.fieldAt(d, k);
        // Whether the field is an array of that type travels with it. Without that, an index into
        // an array field (`g.rows[1]`) would have no element type to answer with and come back a
        // plain long, which is not what `&g.rows[1]` lends.
        return VarType { kind: fd.kind, structName: fd.structName, isArray: fd.isArray };
    }

    // The refusal for a member a type does not have, in the one form every kind of base shares:
    // the type as it is written, then what it does have (`fields `ptr`, `len``, `no fields`).
    noField &self name:Sym ty:String have:str -> never {
        failStr(format("no field `{}` on type `{}`\nnote: `{}` has {}", nameOf(name), ty, ty, have));
    }

    // A named type that is certainly not a struct still waiting to be laid out.
    namesFieldless &self base:VarType -> bool {
        if (base.kind == Lit.TraitObj || base.kind == Lit.Fn) { return true; }
        n: Sym = base.structName;
        return namesScalar(nameOf(n)) || gReg.findEnumSym(n) >= 0 || gReg.findTraitSym(n) >= 0;
    }

    // An array as it is written, `[long; 3]`, for a message. The length when the place says it,
    // else the element type alone.
    spellArrayOf &self inout a:Ast id:NodeId t:VarType -> String {
        s: String;
        s.push('[');
        s.pushString(spellTypeRef(TypeRef { base: t.kind, name: t.structName }));
        n: long = self.placeArrayLen(a, id);
        if (n >= 0) { s.pushStr("; "); s.pushLong(n); }
        s.push(']');
        return s;
    }

    // A value whose type implements `MustUse` may not be computed and thrown away.
    //
    // This is the one half of a `Result` that a library cannot provide. `Result<T, E>` is an
    // ordinary generic struct (nothing about it needs to be in the compiler) but the property
    // that makes it worth having over a negative-errno `long` is that ignoring it is an error,
    // and no library can say that about itself. So the compiler provides the general rule and the
    // standard library provides the type, rather than the compiler knowing what a Result is.
    requireUsed &self inout a:Ast id:NodeId t:VarType -> void {
        if (id == NO_NODE || t.kind != Lit.Struct || t.structName == NO_SYM) { return; }
        // An assignment is a use. It is the value's destination, not a discard.
        if (a.expr(id).op == Op.Assignment) { return; }
        if (!gReg.structImplements(nameOf(t.structName), intern("MustUse"))) { return; }
        failStr(format("unused `{}` that must be used\nnote: `{}` implements `MustUse`, so it carries a failure the caller has to look at\nhelp: bind it (`r: {} = ...`) and check it, or bind it to a name to drop it deliberately",
                       nameOf(t.structName), nameOf(t.structName), nameOf(t.structName)));
    }

    // A slice is a borrowed view. Storing through one is allowed exactly when the caller lent it
    // for that (an `inout` parameter) and the call site said so with `&`, which is what puts the
    // write under the exclusivity check. A local slice is a view and never a lend: a borrow lives
    // only across a call, so there is no call to say `inout` on.
    checkSliceStore &self inout a:Ast lhs:NodeId -> void {
        if (lhs == NO_NODE || self.curFn < 0) { return; }
        p: Payload = a.expr(lhs).payload;
        i: long = -1;
        match p { Index(v) { i = v; } _ { return; } }
        ix: IndexNode = a.indexes.get(i);
        if (ix.whole) { return; }
        n: Sym = self.indexBaseName(a, ix);
        if (n == NO_SYM) { return; }
        n = self.resolveVar(n);
        if (self.lookup(n).kind != Lit.Slice) { return; }
        if (self.paramConvOf(a, self.curFn, n) == Conv.Inout) { return; }
        failStr(format("cannot assign through the slice `{}`\nnote: a slice is a read-only view unless it is an `inout` parameter\nhelp: declare it `inout {}:[T]` and lend it with `&` at the call",
                       nameOf(n), nameOf(n)));
    }

    // A `str` is an immutable view: a literal's bytes live in read-only data, and every other
    // `str` is a view some owner (a `String`, a buffer) lent. `s[i] = v` is refused whatever `s`
    // is; text is built in a `String` or a `[u8]` buffer. Asked once the target is typed.
    // `lt` is what the target was typed: a byte of a `str` is a `u8` whose base is a `str` (an
    // element of an array of `str` is a `str`, and an element of a `[u8; N]` has a `u8` base).
    refuseStrStore &self inout a:Ast lhs:NodeId lt:VarType -> void {
        if (lhs == NO_NODE || lt.kind != Lit.U8) { return; }
        p: Payload = a.expr(lhs).payload;
        i: long = -1;
        match p { Index(v) { i = v; } _ { return; } }
        ix: IndexNode = a.indexes.get(i);
        if (ix.whole || ix.index == NO_NODE) { return; }
        bk: Lit = Lit.Void;
        if (ix.base != NO_NODE) { bk = a.expr(ix.base).kind; }
        else { bt: VarType = self.lookup(self.resolveVar(ix.name)); if (!bt.isArray) { bk = bt.kind; } }
        if (bk != Lit.Str) { return; }
        who: Sym = self.indexBaseName(a, ix);
        what: str = "this `str`";
        if (who != NO_SYM) { what = keepString(format("the `str` `{}`", nameOf(who))); }
        failStr(format("cannot assign to a byte of {}\nnote: a `str` is an immutable view of its bytes\nhelp: build the text in a `String` or a `[u8]` buffer",
                       what));
    }

    // The variable an index was written on, when it was written on one at all: the parser puts
    // the base in `base` as an expression, so a bare name is an `Lvalue` node rather than a name
    // on the index itself.
    indexBaseName &self inout a:Ast ix:IndexNode -> Sym {
        if (ix.base == NO_NODE) { return ix.name; }
        b: Expr = a.expr(ix.base);
        if (b.op != Op.Lvalue) { return NO_SYM; }
        p: Payload = b.payload;
        match p { Name(x) { return x; } _ { } }
        return NO_SYM;
    }

    // `v[i] = x` where `v`'s type implements `IndexSet`: the writing half of indexing, and a
    // separate trait from `Index` because reading and writing are separately possible. Which
    // instantiation is meant is settled afterwards by ordinary method resolution: a type indexed
    // at two key types has two `setAt`s and the argument picks. Answers whether it rewrote.
    tryIndexSet &self inout a:Ast id:NodeId -> bool {
        e: Expr = a.expr(id);
        if (e.left == NO_NODE || e.right == NO_NODE) { return false; }
        p: Payload = a.expr(e.left).payload;
        i: long = -1;
        match p { Index(v) { i = v; } _ { return false; } }
        ix: IndexNode = a.indexes.get(i);
        if (ix.whole || ix.index == NO_NODE) { return false; }
        recv: NodeId = ix.base;
        rt: VarType = varType(Lit.Void, NO_SYM);
        if (recv == NO_NODE) {
            q: Sym = self.resolveVar(ix.name);
            rt = self.lookup(q);
            recv = a.leafOf(Op.Lvalue, Payload.Name(q), rt.kind, rt.structName);
        } else {
            rt = self.checkExpr(a, recv);
        }
        // An array of a type that implements the trait is still an array: its elements are
        // addressed, not asked.
        if (rt.isArray || rt.structName == NO_SYM) { return false; }
        if (!(rt.kind == Lit.Struct || rt.kind == Lit.Ref)) { return false; }
        if (!gReg.structImplements(nameOf(rt.structName), intern("IndexSet"))) { return false; }
        args: Vec<NodeId>;
        args.push(ix.index);
        args.push(e.right);
        a.calls.push(CallNode { name: intern("setAt"), receiver: recv,
                                firstArg: a.addArgs(args), argCount: 2,
                                slot: NO_SLOT, callee: NO_NODE, sigKey: NO_SYM });
        a.setExpr(id, Expr { op: Op.MethodCall, left: NO_NODE, right: NO_NODE, kind: Lit.Void,
                             structName: NO_SYM, isParen: e.isParen,
                             payload: Payload.Call(a.calls.len() - 1) });
        return true;
    }

    // Written onto the node, because the ownership pass needs it and cannot re-derive it: what a
    // raw pointer reaches is nobody's, so a store through one releases nothing. There is no old
    // value known to be there. `v.buf.ptr[v.count] = x` writes one past the end, and saving and
    // releasing "the value being overwritten" there releases whatever the allocator last left.
    noteRawBase &self inout a:Ast i:long -> void {
        ix: IndexNode = a.indexes.get(i);
        ix.rawPointerBase = true;
        a.indexes.set(i, ix);
    }

    // `xs[i]`: the element type. An array or slice yields its element; a pointer its pointee.
    checkIndex &self inout a:Ast id:NodeId i:long -> VarType {
        ix: IndexNode = a.indexes.get(i);
        recv: NodeId = ix.base;
        base: VarType = varType(Lit.Void, NO_SYM);
        if (recv != NO_NODE) { base = self.checkExpr(a, recv); }
        else {
            // The named form: `v[i]`, whose base is a variable rather than an expression. The
            // back end needs the name to find a slot; a dispatch needs it as a receiver.
            q: Sym = self.resolveVar(ix.name);
            base = self.lookup(q);
            recv = a.leafOf(Op.Lvalue, Payload.Name(q), base.kind, base.structName);
        }
        if (ix.index != NO_NODE) { self.checkExpr(a, ix.index); }
        // A range's bounds are expressions like any other (`body[..f(x)]`), and one left
        // unchecked keeps the name it was written with, which resolves to nothing at link time.
        if (ix.sliceStart != NO_NODE) { self.checkExpr(a, ix.sliceStart); }
        if (ix.sliceEnd != NO_NODE) { self.checkExpr(a, ix.sliceEnd); }
        if (ix.whole || ix.sliceStart != NO_NODE || ix.sliceEnd != NO_NODE) {
            // An array or a slice knows its own length, so its bounds are checked and the form is
            // safe. A raw pointer knows nothing: `p[..n]` is the only way to build a {ptr, len}
            // from parts, and every later bounds check on that slice trusts the `n` given here,
            // which is the whole safety story of the form, and why it is the author's to tell.
            // An array of pointers is an array, and knows its length like any other.
            if (base.kind == Lit.Ptr && !base.isArray) {
                // `[..]` takes its length from the declaration, and a pointer has none to give.
                // Saying so beats producing a slice with a made-up length that every later bounds
                // check would then trust.
                if (ix.sliceEnd == NO_NODE) {
                    who: Sym = self.indexBaseName(a, ix);
                    if (who == NO_SYM) { who = intern("this expression"); }
                    failStr(format("cannot slice the pointer `{}` without a length\nnote: a pointer does not know how many elements it points at\nhelp: write `[..n]` to say how many",
                                   nameOf(who)));
                }
                self.requireUnsafe("building a slice from a pointer and a length");
                self.noteRawBase(a, i);
            }
            // Part of a `str` is a `str`: the same bytes, a shorter view.
            if (base.kind == Lit.Str && !base.isArray) { return varType(Lit.Str, NO_SYM); }
            // A struct is no run of elements, whatever it holds: `v[..]` on a `Vec` would make a
            // slice of `Vec`s over the Vec's own three words.
            if ((base.kind == Lit.Struct || base.kind == Lit.Ref || base.kind == Lit.TraitObj) && !base.isArray) {
                hint: str = "";
                if (base.structName != NO_SYM && gReg.structImplements(nameOf(base.structName), intern("AsSlice"))) {
                    hint = "\nhelp: write `.asSlice()` for its elements";
                }
                failStr(format("cannot slice a value of type `{}`{}", self.spellType(base.kind, base.structName), hint));
            }
            // A slice's companion is its element's spelling. An array of a scalar, a `str` or a
            // slice has none of its own, and a slice of it with none would index as a `long`:
            // `ss[..][2]` over a `[str; 3]` would read the first word of the element as the
            // element.
            if (base.isArray && base.kind != Lit.Struct) {
                return varType(Lit.Slice, intern(typeMangleName(base.kind, base.structName)));
            }
            return varType(Lit.Slice, base.structName);
        }
        // An array of T indexes to a T: the element, not the block.
        if (base.isArray) { return varType(base.kind, base.structName); }
        // A `str` is `{ptr, len}` over bytes, so `s[i]` is the byte at `i`, bounds-checked as a
        // `[u8]`'s element is. Typed `long`, it would be read as the eight-byte word at `8 * i`.
        if (base.kind == Lit.Str) { return varType(Lit.U8, NO_SYM); }
        // `v[i]` on a struct is `Index::at`, the same call written by hand, so the element comes
        // back as a borrow and an owning one is read in place rather than copied out.
        if ((base.kind == Lit.Struct || base.kind == Lit.Ref) && base.structName != NO_SYM
            && ix.index != NO_NODE
            && gReg.structImplements(nameOf(base.structName), intern("Index"))) {
            args: Vec<NodeId>;
            args.push(ix.index);
            a.calls.push(CallNode { name: intern("at"), receiver: recv,
                                    firstArg: a.addArgs(args), argCount: 1,
                                    slot: NO_SLOT, callee: NO_NODE, sigKey: NO_SYM });
            c: long = a.calls.len() - 1;
            a.setExpr(id, Expr { op: Op.MethodCall, left: NO_NODE, right: NO_NODE,
                                 kind: Lit.Void, structName: NO_SYM, isParen: false,
                                 payload: Payload.Call(c) });
            return self.checkCall(a, id, c);
        }
        if (base.kind == Lit.Ptr || base.kind == Lit.Slice) {
            // A slice carries its length and is bounds-checked; a raw pointer carries nothing, so
            // there is no length to check the index against.
            if (base.kind == Lit.Ptr) {
                // `for x in xs` reads its element through a pointer it set to the collection's
                // first element and indexes below the length it read with it: the bound is the
                // loop's, and the guard holds the body to leaving the collection alone.
                if (forPointerOf(a, recv) == NO_SYM) { self.requireUnsafe("indexing a raw pointer"); }
                self.noteRawBase(a, i);
            }
            // The element is whatever the companion name spells, decoded: a `**Node` records its
            // pointee as `ptr_Node`, and reading that as a struct of that name leaves `rows[0]`
            // with no pointee and `rows[0][0]` with no element type at all.
            if (base.structName != NO_SYM) {
                elem: TypeRef = unmangledType(nameOf(base.structName));
                return varType(elem.base, elem.name);
            }
        }
        return varType(Lit.Long, NO_SYM);
    }

    // ─── definite initialization ─────────────────────────────────────────────
    //
    // A local must be assigned on every path before it is read, and a Drop-typed one before its
    // scope exits: the automatic release this pass installs would otherwise free whatever the
    // stack happened to hold. What counts as an assignment: `x = ...`, an `asm out x`, a
    // destructuring target, a write to a field of it (partial initialization is accepted as
    // full, a documented gap), and `&x` inside `unsafe`, which is how trusted code is handed a
    // slot to fill. A fixed array is exempt, having no element-wise tracking; a global is zeroed
    // bss and was never in question.
    //
    // Runs before the ownership walk rewrites the body, so it reads the program as written
    // rather than one already carrying flags and releases.
    initFunction &self inout a:Ast at:long -> void {
        self.tracked.clear();
        self.assigned.clear();
        self.initScope.clear();
        self.initBase.clear();
        self.unsafeDepth = 0;
        self.ownFn = at;
        if (a.fns.get(at).isUnsafe) { self.unsafeDepth = 1; }
        self.initBlock(a, a.fns.get(at).body);
    }

    // True when the block cannot fall out of its end: what follows it contributes nothing to
    // "assigned on every path", because no path gets there.
    initBlock &self inout a:Ast b:long -> bool {
        self.initBase.push(self.initScope.len());
        diverged: bool = false;
        n: long = a.blockLen(b);
        k: long = 0;
        while (k < n && !diverged) {
            w: long = a.enterStmt(a.stmtIdAt(b, k));
            diverged = self.initStmt(a, a.stmtAt(b, k));
            gPos = w;
            k = k + 1;
        }
        if (!diverged) { self.initDropExit(a, self.initBase.last()); }
        base: long = self.initBase.last();
        while (self.initScope.len() > base) { self.initScope.pop(); }
        self.initBase.pop();
        return diverged;
    }

    initStmt &self inout a:Ast st:Stmt -> bool {
        if (st.kind == StmtKind.VarDecl) {
            d: VarDeclNode = a.decls.get(st.at);
            if (d.isArray || d.kind == Lit.Void) { return false; }
            // Per declaration: a sibling scope may have declared the same name (the parser gives
            // both one name), and what was or was not assigned there says nothing about this one.
            if (d.init != NO_NODE) {                 // the declaration is the assignment
                self.initScanExpr(a, d.init);
                if (self.tracked.has(nameOf(d.name))) { self.initAssign(d.name); }
                return false;
            }
            self.initUnassign(d.name);
            self.tracked.put(nameOf(d.name), true);
            if (d.kind == Lit.Struct && gReg.needsDrop(d.structName)) { self.initScope.push(d.name); }
            return false;
        }
        if (st.kind == StmtKind.Expr || st.kind == StmtKind.Call) {
            self.initScanExpr(a, a.exprStmts.get(st.at).value);
            // A call to a `-> never` function ends the path: nothing after it runs, and nothing
            // in scope is released (the process ends there).
            return self.neverStmt(a, st);
        }
        if (st.kind == StmtKind.Return) {
            self.initScanExpr(a, a.returns.get(st.at).value);
            self.initDropExit(a, 0);                    // every in-scope release runs here
            return true;
        }
        // Both leave this block as finally as a `return` does.
        if (st.kind == StmtKind.Break || st.kind == StmtKind.Continue) { return true; }
        if (st.kind == StmtKind.If) { return self.initIf(a, st.at); }
        if (st.kind == StmtKind.Match) { return self.initMatch(a, st.at); }
        if (st.kind == StmtKind.While) {
            w: WhileNode = a.whiles.get(st.at);
            self.initScanExpr(a, w.cond);
            entry: Vec<Sym>;
            self.initSnapshot(&entry);
            self.initBlock(a, w.body);               // the body may run zero times...
            if (w.step >= 0) { self.initBlock(a, w.step); }
            self.initRestore(&entry);                // ...so what it assigns does not survive
            return false;
        }
        if (st.kind == StmtKind.Loop) {
            entry: Vec<Sym>;
            self.initSnapshot(&entry);
            self.initBlock(a, a.blockStmts.get(st.at).body);
            self.initRestore(&entry);
            return false;
        }
        if (st.kind == StmtKind.Unsafe || st.kind == StmtKind.Block) {
            was: long = self.unsafeDepth;
            if (st.kind == StmtKind.Unsafe) { self.unsafeDepth = self.unsafeDepth + 1; }
            d: bool = self.initBlock(a, a.blockStmts.get(st.at).body);
            self.unsafeDepth = was;
            return d;
        }
        if (st.kind == StmtKind.With) { return self.initBlock(a, a.withs.get(st.at).body); }
        // The handler can be entered from any point in the body, where nothing the body assigned
        // can be counted on, so it starts from what was assigned before the statement. After it,
        // what both the body and the handler assign is assigned, as after an `if` and its `else`.
        if (st.kind == StmtKind.Recover) {
            w: WhileNode = a.whiles.get(st.at);
            entry: Vec<Sym>; meet: Vec<Sym>;
            self.initSnapshot(&entry);
            bodyExits: bool = self.initBlock(a, w.body);
            if (!bodyExits) { self.initSnapshot(&meet); }
            self.initRestore(&entry);
            handlerExits: bool = self.initBlock(a, w.step);
            if (bodyExits && handlerExits) { self.initRestore(&entry); return true; }
            if (bodyExits) { return false; }
            if (!handlerExits) { self.initIntersect(&meet); }
            self.initRestore(&meet);
            return false;
        }
        if (st.kind == StmtKind.Asm) {
            nd: AsmNode = a.asms.get(st.at);
            for k in 0..nd.pieceCount {
                p: AsmPiece = a.asmPieces.get(nd.firstPiece + k);
                if (p.kind == AsmKind.Out) { self.initAssign(p.name); }
                else { self.initScanExpr(a, p.value); }
            }
            return nd.noReturn;
        }
        if (st.kind == StmtKind.Destructure) {
            ds: DestructureNode = a.destructures.get(st.at);
            self.initScanExpr(a, ds.value);
            for k in 0..ds.nameCount { self.initAssign(a.names.get(ds.firstName + k)); }
            return false;
        }
        return false;
    }

    // An `if` chain assigns something afterwards only when it is total: a bare `else` is parsed
    // as a link whose condition always holds, and without one the whole chain may be skipped.
    initIf &self inout a:Ast at:long -> bool {
        entry: Vec<Sym>; meet: Vec<Sym>;
        self.initSnapshot(&entry);
        total: bool = false;
        any: bool = false;
        allDiverge: bool = true;
        c: long = at;
        while (c >= 0) {
            nd: IfNode = a.ifs.get(c);
            if (self.initAlways(a, nd.cond)) { total = true; }
            self.initRestore(&entry);
            self.initScanExpr(a, nd.cond);
            self.initRestore(&entry);
            if (self.initBlock(a, nd.body)) { c = nd.elseIf; continue; }
            allDiverge = false;
            if (!any) { self.initSnapshot(&meet); any = true; }
            else { self.initIntersect(&meet); }
            c = nd.elseIf;
        }
        if (total && any) { self.initRestore(&meet); }
        else { self.initRestore(&entry); }
        return total && allDiverge;
    }

    // A `match` is exhaustive, so every path really does go through an arm and what all of them
    // assign is assigned afterwards, where an `if` with no `else` has to fall back.
    initMatch &self inout a:Ast at:long -> bool {
        m: MatchNode = a.matches.get(at);
        entry: Vec<Sym>; meet: Vec<Sym>;
        self.initSnapshot(&entry);
        any: bool = false;
        for k in 0..m.armCount {
            arm: ArmNode = a.arms.get(m.firstArm + k);
            self.initRestore(&entry);
            self.initScanExpr(a, arm.test);
            self.initRestore(&entry);
            if (!self.initBlock(a, arm.body)) {
                if (!any) { self.initSnapshot(&meet); any = true; }
                else { self.initIntersect(&meet); }
            }
        }
        if (any) { self.initRestore(&meet); return false; }
        self.initRestore(&entry);
        if (m.armCount > 0) { self.initDropExit(a, 0); return true; }   // every arm returned
        return false;
    }

    // A condition the parser wrote for a bare `else`: a literal that always holds.
    initAlways &self inout a:Ast id:NodeId -> bool {
        if (id == NO_NODE) { return true; }
        e: Expr = a.expr(id);
        if (e.op != Op.Literal) { return false; }
        p: Payload = e.payload;
        match p { Num(v) { return v != 0; } _ { } }
        return false;
    }

    // A read of a tracked-but-unassigned local is the error; `&x` is where it gets subtle.
    initScanExpr &self inout a:Ast id:NodeId -> void {
        if (id == NO_NODE) { return; }
        e: Expr = a.expr(id);
        if (e.op == Op.Assignment) { self.initApplyAssign(a, id); return; }
        if (e.left != NO_NODE || e.right != NO_NODE) {
            self.initScanExpr(a, e.left);
            self.initScanExpr(a, e.right);
            return;
        }
        p: Payload = e.payload;
        match p {
            Name(n) {
                if (e.op == Op.Lvalue) { self.initRead(a, n); }
            }
            Sub(v) {
                if (e.op != Op.AddressOf) { self.initScanExpr(a, v); return; }
                self.initAddressOf(a, v, self.unsafeDepth == 0);
            }
            Field(f) { self.initScanExpr(a, a.fields.get(f).base); }
            Index(i) {
                ix: IndexNode = a.indexes.get(i);
                self.initScanExpr(a, ix.index);
                self.initScanExpr(a, ix.sliceStart);
                self.initScanExpr(a, ix.sliceEnd);
                self.initScanExpr(a, ix.base);
            }
            Call(c) {
                cn: CallNode = a.calls.get(c);
                self.initScanExpr(a, cn.receiver);
                self.initScanExpr(a, cn.callee);
                // Inside `unsafe`, `&x` handed straight to a parameter that lends (`inout p:T`) is
                // still a lend, which the callee may read; only a raw address (`&x as long`, or
                // `&x` into a `*T` or integer parameter) is trusted code's to fill.
                at: long = -2;
                for k in 0..cn.argCount {
                    arg: NodeId = a.argAt(cn, k);
                    ae: Expr = a.expr(arg);
                    lent: NodeId = NO_NODE;
                    if (self.unsafeDepth > 0 && ae.op == Op.AddressOf) {
                        if (at == -2) { at = self.fnNodeOf(cn.name); }
                        if (self.initLendParam(a, at, cn, k)) {
                            p: Payload = ae.payload;
                            match p { Sub(v) { lent = v; } _ { } }
                        }
                    }
                    if (lent != NO_NODE) { self.initAddressOf(a, lent, true); }
                    else { self.initScanExpr(a, arg); }
                }
            }
            Lit(l) {
                ln: LitNode = a.lits.get(l);
                self.initScanExpr(a, ln.rest);
                for k in 0..ln.initCount {
                    self.initScanExpr(a, a.inits.get(ln.firstInit + k).value);
                }
            }
            _ { }
        }
    }

    // `&x`, `&x.f`, `&x[i]`. A lend (`lends`: safe code, or a lend position inside `unsafe`) hands
    // the place to a callee that may read it, so the local it is rooted in must hold something
    // already: lending a field of a local declared without a value is refused as reading it is
    // (otherwise `a: Attr; swapValues(&a.name, &self.attrName)` would swap stack garbage into a
    // live String). A raw address inside `unsafe` hands the slot to trusted code to fill (the
    // `memcpy(&r as long, ...)` idiom), and counts as the assignment.
    initAddressOf &self inout a:Ast v:NodeId lends:bool -> void {
        root: Sym = self.initRootOf(a, v);
        if (root == NO_SYM) { self.initScanExpr(a, v); return; }
        if (lends) { self.initRead(a, root); }
        self.initAssign(root);
    }

    // Does argument `k` of this call lend (an `inout` parameter, or one taking a struct), rather
    // than take a raw address? Unknown callees (a fn value, a dispatch) count as lending.
    initLendParam &self inout a:Ast at:long cn:CallNode k:long -> bool {
        if (at < 0) { return cn.slot != NO_SLOT; }
        f: FnNode = a.fns.get(at);
        i: long = k;
        if (cn.receiver != NO_NODE && f.argCount > 0 && nameOf(a.paramAt(f, 0).name) == "self") { i = k + 1; }
        if (i >= f.argCount) { return false; }
        p: VarDeclNode = a.paramAt(f, i);
        return p.conv == Conv.Inout || p.kind == Lit.Ref || p.kind == Lit.Struct || p.kind == Lit.Slice;
    }

    // The right-hand side is read first; then a write anywhere in the left-hand chain
    // initializes the variable that chain is rooted in.
    initApplyAssign &self inout a:Ast id:NodeId -> void {
        e: Expr = a.expr(id);
        self.initScanExpr(a, e.right);
        root: Sym = self.initRootOf(a, e.left);
        if (root != NO_SYM) { self.initAssign(root); return; }
        self.initScanExpr(a, e.left);              // `*p = v` and the like: the base is a read
    }

    // The variable a place chain bottoms out at. Any index along the way is a read, and is
    // scanned as one on the way past.
    initRootOf &self inout a:Ast id:NodeId -> Sym {
        cur: NodeId = id;
        while (cur != NO_NODE) {
            e: Expr = a.expr(cur);
            p: Payload = e.payload;
            match p {
                Name(x) {
                    if (e.op == Op.Lvalue) { return x; }
                    return NO_SYM;
                }
                Field(f) { cur = a.fields.get(f).base; }
                Index(i) {
                    ix: IndexNode = a.indexes.get(i);
                    self.initScanExpr(a, ix.index);
                    self.initScanExpr(a, ix.sliceStart);
                    self.initScanExpr(a, ix.sliceEnd);
                    if (ix.base == NO_NODE) { return ix.name; }
                    cur = ix.base;
                }
                _ { return NO_SYM; }
            }
        }
        return NO_SYM;
    }

    initRead &self inout a:Ast n:Sym -> void {
        if (!self.tracked.has(nameOf(n))) { return; }
        if (self.isAssigned(n)) { return; }
        failStr(format("use of possibly uninitialized variable `{}`", nameOf(n)));
    }

    // Every in-scope Drop local from `from` outward must hold something: its release is about
    // to run, and releasing whatever the stack held is not a diagnostic anyone gets to see.
    initDropExit &self inout a:Ast from:long -> void {
        for k in from..self.initScope.len() {
            n: Sym = self.initScope.get(k);
            if (!self.isAssigned(n)) {
                failStr(format("possibly uninitialized variable `{}` is released at the end of its scope\nnote: its type implements `Drop`, so the automatic release would free garbage\nhelp: initialize it on every path",
                               nameOf(n)));
            }
        }
    }

    isAssigned &self n:Sym -> bool {
        for k in 0..self.assigned.len() {
            if (self.assigned.get(k) == n) { return true; }
        }
        return false;
    }
    initAssign &self n:Sym -> void {
        if (n == NO_SYM || self.isAssigned(n)) { return; }
        self.assigned.push(n);
    }
    initUnassign &self n:Sym -> void {
        for k in 0..self.assigned.len() {
            if (self.assigned.get(k) == n) { self.assigned.removeAt(k); return; }
        }
    }
    initSnapshot &self inout dst:Vec<Sym> -> void {
        dst.clear();
        for k in 0..self.assigned.len() { dst.push(self.assigned.get(k)); }
    }
    initRestore &self inout src:Vec<Sym> -> void {
        self.assigned.clear();
        self.assigned.extend(src);
    }
    // The meet: only what both this path and the running intersection assign survives.
    initIntersect &self inout meet:Vec<Sym> -> void {
        k: long = 0;
        while (k < meet.len()) {
            if (self.isAssigned(meet.get(k))) { k = k + 1; }
            else { meet.removeAt(k); }
        }
    }

    // ─── ownership: moves and automatic release ──────────────────────────────
    //
    // A `Drop` type is move-only, and the compiler is what releases it, exactly once. Every
    // tracked value gets a hidden `__moved_<name>` flag, 0 while it still owns the resource; a
    // move sets it, and each scope exit emits `if (__moved_x == 0) { x.drop(); }` in reverse
    // declaration order. The flag is what makes a conditional move correct with no flow merge
    // at all: which path ran is a runtime fact, and the flag is where that fact is written.
    //
    // Over the whole page rather than per body, because who releases an argument is the
    // callee's answer (`inferConventions`) and no caller can be judged before every callee has
    // given it.
    ownRun &self inout a:Ast page:long -> void {
        self.dropGlue(a, page);
        self.inferConventions(a, page);
        n: long = a.blockLen(page);
        k: long = 0;
        // Which subjects are borrows is settled now that every parameter's convention is.
        while (k < n) {
            st: Stmt = a.stmtAt(page, k);
            if (st.kind == StmtKind.FunctionDef && !a.fns.get(st.at).isTemplate
                && a.fns.get(st.at).body >= 0 && !isUnchecked(st.at)) {
                gPos = a.stmtPos.get(a.stmtIdAt(page, k));
                self.ownGuarded(a, st.at, false);
            }
            k = k + 1;
        }
        if (gErrorCount > 0) { return; }
        for k in 0..n {
            st: Stmt = a.stmtAt(page, k);
            // A dependency's body is not this compile's to rewrite, unless it was checked here for
            // the evaluator, which runs it as the ownership pass leaves it.
            if (st.kind == StmtKind.FunctionDef && !a.fns.get(st.at).isTemplate
                && a.fns.get(st.at).body >= 0 && !isUnchecked(st.at)) {
                gPos = a.stmtPos.get(a.stmtIdAt(page, k));
                self.ownGuarded(a, st.at, true);
            }
        }
        gPos = 0;
        gCtxFn = NO_SYM;
        gCtxInst = NO_SYM;
    }

    // One function's match borrows (`whole` false) or its definite-initialization and ownership
    // walks (`whole` true), in the body of a `recover` as the typing is (`checkGuarded`): every
    // function's first error is reported, and the phase stops after the last function.
    ownGuarded &self inout a:Ast at:long whole:bool -> void {
        enterFn(a.fns.get(at).name);
        if (!canRecover()) { self.ownStep(a, at, whole); return; }
        unsafe { recover { self.ownStep(a, at, whole); } else { } }
    }
    ownStep &self inout a:Ast at:long whole:bool -> void {
        if (!whole) { self.borrowMatches(a, at); return; }
        self.initFunction(a, at);           // before the body gains flags and releases
        self.ownFunction(a, at);
    }

    // ─── a match through a borrow ────────────────────────────────────────────
    //
    // An arm's binding is `v = subject.$V$k;` at its head, which copies the payload into a local
    // the arm owns and releases at its end. That is right when the function owns the subject:
    // the store is a move, recorded on the subject's flag. When the subject is only borrowed (a
    // `&self`, an `inout` or `read` parameter, a `for r: &T` variable, a global, a field reached
    // through one of those) there is no flag to record it on, and the arm would release what the
    // owner still holds: a double release, or a live subtree freed under a tree walk. So there, a
    // binding of an owning payload is a borrow of the payload where it lies, as Rust binds
    // through a reference: the local becomes a `Ref` and its store takes the payload's address.
    // It owns nothing, so the arm's end releases nothing; it cannot be moved out
    // (`ownRejectMove` refuses a borrow that is not a parameter); writing through it writes the
    // matched value; and while the arm holds it, nothing else in the arm may write the matched
    // value (`bmArmBlock`), since that could release the payload under it.
    //
    // A payload that owns nothing has nothing to release twice, and a binding the arm only reads
    // may stay a copy. One the arm writes through may not: the write would land in the copy and
    // be lost. So where a write through a binding lands in someone else's value (`bmLending`: the
    // subject is borrowed, and not a by-value parameter that is passed as a borrow only because the
    // body reads it), no binding may be assigned as a whole (`bmPlainBinds`), and a struct binding
    // becomes a borrow, as an owning one does, if the arm writes through it. Which methods write
    // `self` is known only to the guard's write masks, so it decides (`gCopyBinds`).
    //
    // After convention inference, because a parameter a match takes a payload out of is a sink
    // and so owned, and before the ownership walk, which then meets an ordinary borrow local.
    borrowMatches &self inout a:Ast at:long -> void {
        f: FnNode = a.fns.get(at);
        self.bmLocals.clear();
        if (self.bmOwnRead.len() > 0) { self.bmOwnRead.clear(); }
        if (self.bmCopies.len() > 0) { self.bmCopies.clear(); }
        for k in 0..f.argCount {
            p: VarDeclNode = a.paramAt(f, k);
            self.bmLocals.put(nameOf(p.name), p.kind == Lit.Ref);
            if (p.kind == Lit.Ref && p.conv == Conv.Read) { self.bmOwnRead.put(nameOf(p.name), true); }
        }
        self.bmBlock(a, f.body, at);
    }

    // A local that is a borrow, or a name that is no local at all: a global, which the
    // function never owns either.
    bmIsBorrow &self n:Sym -> bool {
        hit: Option<bool> = self.bmLocals.find(nameOf(n));
        match hit { Some(r) { return r; } None { } }
        return true;
    }

    // Whether a write through a binding of `n`'s payload writes a value this function does not own:
    // `n` is a borrow (an `inout` or `&T` parameter, a `&self`, a borrow local), a global, or a copy
    // noted for the guard, which stands for the borrow it may become. A by-value parameter is the
    // function's own value even where it arrives as a borrow because the body only reads it.
    bmLending &self n:Sym -> bool {
        if (self.bmCopies.len() > 0 && self.bmCopies.has(nameOf(n))) { return true; }
        if (self.bmOwnRead.len() > 0 && self.bmOwnRead.has(nameOf(n))) { return false; }
        return self.bmIsBorrow(n);
    }

    // The copy in `gCopyBinds` that `n` is, or -1.
    bmCopyOf &self n:Sym -> long {
        if (n == NO_SYM || self.bmCopies.len() == 0) { return -1; }
        hit: Option<long> = self.bmCopies.find(nameOf(n));
        match hit { Some(i) { return i; } None { } }
        return -1;
    }

    bmBlock &self inout a:Ast b:long fnAt:long -> void {
        if (b < 0) { return; }
        n: long = a.blockLen(b);
        for k in 0..n {
            a.enterStmt(a.stmtIdAt(b, k));
            st: Stmt = a.stmtAt(b, k);
            if (st.kind == StmtKind.VarDecl) {
                d: VarDeclNode = a.decls.get(st.at);
                self.bmLocals.put(nameOf(d.name), d.kind == Lit.Ref);
                // A sibling scope's local of the same name as a copy is not that copy.
                ci: long = self.bmCopyOf(d.name);
                if (ci >= 0 && gCopyBinds.get(ci).decl != st.at) { self.bmCopies.remove(nameOf(d.name)); }
                if (strStartsWith(nameOf(d.name), "$tup")) { self.bmDestructure(a, b, k, fnAt); }
            } else if (st.kind == StmtKind.If) {
                c: long = st.at;
                while (c >= 0) {
                    nd: IfNode = a.ifs.get(c);
                    self.bmBlock(a, nd.body, fnAt);
                    c = nd.elseIf;
                }
            } else if (st.kind == StmtKind.While) {
                w: WhileNode = a.whiles.get(st.at);
                self.bmForLoop(a, w.body);
                self.bmBlock(a, w.body, fnAt);
                if (w.step >= 0) { self.bmBlock(a, w.step, fnAt); }
            } else if (st.kind == StmtKind.Recover) {
                self.bmBlock(a, a.whiles.get(st.at).body, fnAt);
                self.bmBlock(a, a.whiles.get(st.at).step, fnAt);
            } else if (st.kind == StmtKind.Loop || st.kind == StmtKind.Unsafe || st.kind == StmtKind.Block) {
                self.bmBlock(a, a.blockStmts.get(st.at).body, fnAt);
            } else if (st.kind == StmtKind.With) {
                self.bmBlock(a, a.withs.get(st.at).body, fnAt);
            } else if (st.kind == StmtKind.Match) {
                self.bmMatch(a, b, k, fnAt);
            }
        }
    }

    // `for x in xs`: the parser wrote `x: T; x = $forpK[$foriK];` at the head of the body, a copy
    // of the element. A struct element becomes a borrow of the element where it lies instead,
    // `x: &T; x = &$forpK[$foriK];`, the way a match through a borrow binds: nothing is copied,
    // nothing is moved out of the collection, and nothing is released at the turn's end. A
    // scalar (a backed enum, a `str` and a fn included) is a value, and stays the copy. In the
    // lending form, `for x in &xs`, an element that is not a struct is refused: writing through
    // `x` would write the copy. What the body may do with `x` and `xs` is the guard's to hold
    // (`ConstGuard.holdLoop`): it needs every callee's write mask, which only it has.
    bmForLoop &self inout a:Ast body:long -> void {
        ptr: Sym = forLoopPtr(a, body);
        if (ptr == NO_SYM) { return; }
        ds: Stmt = a.stmtAt(body, 0);
        asn: NodeId = a.exprStmts.get(a.stmtAt(body, 1).at).value;
        d: VarDeclNode = a.decls.get(ds.at);
        if (a.expr(a.expr(asn).right).op == Op.AddressOf) { return; }    // already a borrow
        if (d.kind == Lit.Struct && !namedScalar(d.kind, d.structName)) {
            borrowRetype(a, ds.at, asn);
            restampBlock(a, body, d.name);
            self.bmLocals.put(nameOf(d.name), true);
            return;
        }
        if (forLends(ptr)) {
            failStr(format("cannot lend the elements in `for {} in &...`\nnote: `for x in &xs` lends each element, which needs struct elements, and an element of type `{}` is copied\nhelp: write `xs[i] = ...` to change one",
                           nameOf(d.name), self.spellType(d.kind, d.structName)));
        }
    }

    bmMatch &self inout a:Ast b:long k:long fnAt:long -> void {
        matchAt: long = a.stmtAt(b, k).at;
        m: MatchNode = a.matches.get(matchAt);
        subj: Sym = m.scrutinee;
        borrowed: bool = self.bmIsBorrow(subj);
        lending: bool = self.bmLending(subj);
        copyOf: long = self.bmCopyOf(subj);   // the copy the subject is, which its bindings are read out of
        matchPos: long = gPos;
        // The path the arms' borrows point into, which is what the arms may not write.
        held: Vec<Sym>;
        held.push(subj);
        // `match h.f` is the parser's `$matchN: F; $matchN = h.f;` right ahead of the match, in a
        // block of its own. Copying an owning field out of a borrowed `h` is the same double
        // release one level up, so the hidden local becomes a borrow of the field, and the match
        // one through a borrow.
        // `match &x` and `match &x.f` (`$bmatchN`) borrow whatever `x` is: the arms only read,
        // so an owned `x` stays whole.
        explicit: bool = strStartsWith(nameOf(subj), "$bmatch");
        if ((explicit || strStartsWith(nameOf(subj), "$match")) && k >= 2) {
            ds: Stmt = a.stmtAt(b, k - 2);
            ss: Stmt = a.stmtAt(b, k - 1);
            if (ds.kind == StmtKind.VarDecl && ss.kind == StmtKind.Expr && a.decls.get(ds.at).name == subj) {
                d: VarDeclNode = a.decls.get(ds.at);
                asn: NodeId = a.exprStmts.get(ss.at).value;
                src: NodeId = a.expr(asn).right;
                root: Sym = self.ownPlaceRoot(a, src);
                if (d.kind == Lit.Struct && gReg.needsDrop(d.structName)
                    && (explicit || (root != NO_SYM && self.bmIsBorrow(root)))) {
                    borrowRetype(a, ds.at, asn);
                    restampBlock(a, b, subj);
                    self.bmLocals.put(nameOf(subj), true);
                    borrowed = true;
                    lending = explicit || self.bmLending(root);
                    held.clear();
                    self.xPath.clear();
                    if (self.pathOf(a, src) > 0) { held.extend(self.xPath); }
                } else if (d.kind == Lit.Struct && !gReg.needsDrop(d.structName) && !namedScalar(d.kind, d.structName)
                           && root != NO_SYM && (explicit || self.bmLending(root))) {
                    // A subject that owns nothing, read into a copy: a borrow of the place once
                    // a binding of it is one.
                    self.xPath.clear();
                    if (self.pathOf(a, src) > 0) {
                        gCopyBinds.push(CopyBind { name: subj, decl: ds.at, store: asn, body: b, subject: true,
                                                   viaRef: false, parent: self.bmCopyOf(root), fnName: a.fns.get(fnAt).name,
                                                   conflict: "", conflictPos: 0 });
                        copyOf = gCopyBinds.len() - 1;
                        self.bmCopies.put(nameOf(subj), copyOf);
                        lending = true;
                        held.clear();
                        held.extend(self.xPath);
                    }
                }
            }
        }
        for j in 0..m.armCount {
            // The bindings that stay copies unless the arm writes through them.
            if (lending) { self.bmPlainBinds(a, m.firstArm + j, &held, copyOf, matchPos, fnAt); }
            arm: ArmNode = a.arms.get(m.firstArm + j);
            made: Vec<Sym>;           // the bindings this arm makes borrows
            stores: Vec<NodeId>;      // and the stores that take their addresses
            if (borrowed) {
                for i in 0..arm.bindCount {
                    nm: Sym = a.names.get(arm.firstBind + i);
                    if (nameOf(nm) == "_") { continue; }
                    s: long = self.bmOwningBinding(a, arm.body, nm);
                    if (s < 0) { continue; }
                    di: long = a.stmtAt(arm.body, s).at;
                    asn: NodeId = a.exprStmts.get(a.stmtAt(arm.body, s + 1).at).value;
                    borrowRetype(a, di, asn);
                    restampBlock(a, arm.body, nm);
                    made.push(nm);
                    stores.push(asn);
                }
            } else { self.bmTakeRest(a, m.firstArm + j); }
            if (made.len() > 0) {
                armPos: long = gPos;
                self.bmArmBlock(a, arm.body, &held, &made, &stores, fnAt);
                self.bmHoldGlobal(&held, arm.body, armPos, fnAt, made.get(0), -1, a.fns.get(fnAt).name, false);
            }
            self.bmBlock(a, a.arms.get(m.firstArm + j).body, fnAt);
        }
    }

    // An arm holding a borrow into a `var` global: what it calls may write the global by name,
    // which only the guard can tell (`ConstGuard.holdArms`). `copy` is the binding in `gCopyBinds`
    // the arm holds only if the guard makes it a borrow, or -1.
    bmHoldGlobal &self inout held:Vec<Sym> body:long pos:long fnAt:long made:Sym copy:long fnName:Sym destr:bool -> void {
        if (held.len() == 0) { return; }
        root: Sym = self.resolveVar(held.get(0));
        gi: long = gReg.findGlobalSym(root);
        if (gi < 0 || !gReg.globalDef(gi).isVar || self.locals.has(nameOf(root))) { return; }
        // The fields under the global the arm borrows into, up to an element.
        path: Vec<Sym>;
        path.push(root);
        for i in 1..held.len() {
            if (charAt(nameOf(held.get(i)), 0) == '[') { path.push(intern("*")); break; }
            path.push(held.get(i));
        }
        gHeldArms.push(HeldArm { body: body, global: root, pos: pos, fnName: fnName, made: made, path: path, copy: copy, destr: destr });
    }

    // The bindings of arm `armAt` of a match whose bindings write what someone else owns
    // (`bmLending`), other than the owning ones (`bmMatch` makes those borrows). Each names the
    // payload where it lies, so none may be given another value as a whole (`bmCopyWalk`). A
    // struct one is a copy while the arm only reads it and a borrow of the payload where the arm
    // writes through it, which the guard decides (`gCopyBinds`); so that a borrow is held to what
    // one allows, what the arm does that `bmArmBlock` would refuse is found now and kept with it.
    bmPlainBinds &self inout a:Ast armAt:long inout held:Vec<Sym> parent:long matchPos:long fnAt:long -> void {
        arm: ArmNode = a.arms.get(armAt);
        if (arm.bindCount == 0) { return; }
        names: Vec<Sym>;
        scalar: Vec<bool>;
        decls: Vec<long>;
        stores: Vec<NodeId>;
        for i in 0..arm.bindCount {
            nm: Sym = a.names.get(arm.firstBind + i);
            if (nameOf(nm) == "_") { continue; }
            s: long = bindingAt(a, arm.body, nm);
            if (s < 0) { continue; }
            d: VarDeclNode = a.decls.get(a.stmtAt(arm.body, s).at);
            if (d.kind == Lit.Struct && gReg.needsDrop(d.structName)) { continue; }
            names.push(nm);
            scalar.push(d.kind != Lit.Struct || d.isArray || namedScalar(d.kind, d.structName));
            decls.push(a.stmtAt(arm.body, s).at);
            stores.push(a.exprStmts.get(a.stmtAt(arm.body, s + 1).at).value);
        }
        if (names.len() == 0) { return; }
        self.bmCopyWalk(a, arm.body, 0, &names, &scalar, &stores, &held, armAt, false);
        fnName: Sym = a.fns.get(fnAt).name;
        for i in 0..names.len() {
            if (scalar.get(i)) { continue; }
            gCopyBinds.push(CopyBind { name: names.get(i), decl: decls.get(i), store: stores.get(i), body: arm.body,
                                       subject: false, viaRef: false, parent: parent, fnName: fnName,
                                       conflict: "", conflictPos: 0 });
            ci: long = gCopyBinds.len() - 1;
            self.bmCopies.put(nameOf(names.get(i)), ci);
            made: Vec<Sym>;
            made.push(names.get(i));
            self.bmDry = ci;
            self.bmArmBlock(a, arm.body, held, &made, &stores, fnAt);
            self.bmDry = -1;
            self.bmHoldGlobal(held, arm.body, matchPos, fnAt, names.get(i), ci, fnName, false);
        }
    }

    // A binding in `names` assigned as a whole, or a scalar one lent to an `inout` parameter, which
    // would assign it: refused, from statement `from` of block `b` on. The binding is the payload or
    // element where it lies, and a variant's payload is replaced with the variant, an element by
    // assigning it where the tuple lies. `inUnsafe`: inside `unsafe`, where `&n` of a scalar may be a
    // raw address rather than a lend. `armAt` is the arm, for the message, or -1 for a destructure.
    bmCopyWalk &self inout a:Ast b:long from:long inout names:Vec<Sym> inout scalar:Vec<bool> inout stores:Vec<NodeId>
               inout held:Vec<Sym> armAt:long inUnsafe:bool -> void {
        if (b < 0) { return; }
        n: long = a.blockLen(b);
        for k in from..n {
            a.enterStmt(a.stmtIdAt(b, k));
            st: Stmt = a.stmtAt(b, k);
            if (st.kind == StmtKind.VarDecl) { self.bmCopyExpr(a, a.decls.get(st.at).init, names, scalar, stores, held, armAt, inUnsafe); }
            else if (st.kind == StmtKind.Expr || st.kind == StmtKind.Call) {
                self.bmCopyExpr(a, a.exprStmts.get(st.at).value, names, scalar, stores, held, armAt, inUnsafe);
            }
            else if (st.kind == StmtKind.Return) { self.bmCopyExpr(a, a.returns.get(st.at).value, names, scalar, stores, held, armAt, inUnsafe); }
            else if (st.kind == StmtKind.If) {
                c: long = st.at;
                while (c >= 0) {
                    nd: IfNode = a.ifs.get(c);
                    self.bmCopyExpr(a, nd.cond, names, scalar, stores, held, armAt, inUnsafe);
                    self.bmCopyWalk(a, nd.body, 0, names, scalar, stores, held, armAt, inUnsafe);
                    c = nd.elseIf;
                }
            } else if (st.kind == StmtKind.While || st.kind == StmtKind.Recover) {
                w: WhileNode = a.whiles.get(st.at);
                self.bmCopyExpr(a, w.cond, names, scalar, stores, held, armAt, inUnsafe);
                self.bmCopyWalk(a, w.body, 0, names, scalar, stores, held, armAt, inUnsafe);
                if (w.step >= 0) { self.bmCopyWalk(a, w.step, 0, names, scalar, stores, held, armAt, inUnsafe); }
            } else if (st.kind == StmtKind.Loop || st.kind == StmtKind.Block) {
                self.bmCopyWalk(a, a.blockStmts.get(st.at).body, 0, names, scalar, stores, held, armAt, inUnsafe);
            } else if (st.kind == StmtKind.Unsafe) {
                self.bmCopyWalk(a, a.blockStmts.get(st.at).body, 0, names, scalar, stores, held, armAt, true);
            } else if (st.kind == StmtKind.With) {
                self.bmCopyWalk(a, a.withs.get(st.at).body, 0, names, scalar, stores, held, armAt, inUnsafe);
            } else if (st.kind == StmtKind.Match) {
                m: MatchNode = a.matches.get(st.at);
                for i in 0..m.armCount {
                    arm: ArmNode = a.arms.get(m.firstArm + i);
                    self.bmCopyExpr(a, arm.test, names, scalar, stores, held, armAt, inUnsafe);
                    self.bmCopyWalk(a, arm.body, 0, names, scalar, stores, held, armAt, inUnsafe);
                }
            } else if (st.kind == StmtKind.Destructure) {
                self.bmCopyExpr(a, a.destructures.get(st.at).value, names, scalar, stores, held, armAt, inUnsafe);
            }
        }
    }

    bmCopyExpr &self inout a:Ast id:NodeId inout names:Vec<Sym> inout scalar:Vec<bool> inout stores:Vec<NodeId>
               inout held:Vec<Sym> armAt:long inUnsafe:bool -> void {
        if (id == NO_NODE) { return; }
        // A leaf (a name, a literal) is neither a store nor a call, and has nothing under it.
        lo: Op = a.exprs[id].op;
        if (lo == Op.Lvalue || lo == Op.Literal || lo == Op.StringLit) { return; }
        e: Expr = a.expr(id);
        if (e.op == Op.Assignment && !nodeIn(stores, id)) {
            x: Sym = self.convBareName(a, e.left);
            if (x != NO_SYM && symIn(names, x)) { self.bmWholeWrite(a, x, names, scalar, stores, held, armAt, ""); }
        }
        self.bmCopyExpr(a, e.left, names, scalar, stores, held, armAt, inUnsafe);
        self.bmCopyExpr(a, e.right, names, scalar, stores, held, armAt, inUnsafe);
        p: Payload = e.payload;
        match p {
            Sub(v)   { self.bmCopyExpr(a, v, names, scalar, stores, held, armAt, inUnsafe); }
            Field(f) { self.bmCopyExpr(a, a.fields.get(f).base, names, scalar, stores, held, armAt, inUnsafe); }
            Index(i) {
                ix: IndexNode = a.indexes.get(i);
                self.bmCopyExpr(a, ix.base, names, scalar, stores, held, armAt, inUnsafe);
                self.bmCopyExpr(a, ix.index, names, scalar, stores, held, armAt, inUnsafe);
                self.bmCopyExpr(a, ix.sliceStart, names, scalar, stores, held, armAt, inUnsafe);
                self.bmCopyExpr(a, ix.sliceEnd, names, scalar, stores, held, armAt, inUnsafe);
            }
            Call(c) {
                cn: CallNode = a.calls.get(c);
                self.bmScalarLends(a, cn, names, scalar, stores, held, armAt, inUnsafe);
                self.bmCopyExpr(a, cn.receiver, names, scalar, stores, held, armAt, inUnsafe);
                self.bmCopyExpr(a, cn.callee, names, scalar, stores, held, armAt, inUnsafe);
                for k in 0..cn.argCount { self.bmCopyExpr(a, a.argAt(cn, k), names, scalar, stores, held, armAt, inUnsafe); }
            }
            Lit(l) {
                ln: LitNode = a.lits.get(l);
                self.bmCopyExpr(a, ln.rest, names, scalar, stores, held, armAt, inUnsafe);
                for k in 0..ln.initCount {
                    self.bmCopyExpr(a, a.inits.get(ln.firstInit + k).value, names, scalar, stores, held, armAt, inUnsafe);
                }
            }
            _ { }
        }
    }

    // `&n` of a scalar binding handed to a call: a lend to an `inout` scalar parameter, which may
    // assign it. Anything else it can be is a raw address, which `unsafe` alone takes and answers
    // for, so inside `unsafe` only a parameter known to be an `inout` scalar counts.
    bmScalarLends &self inout a:Ast cn:CallNode inout names:Vec<Sym> inout scalar:Vec<bool> inout stores:Vec<NodeId>
                  inout held:Vec<Sym> armAt:long inUnsafe:bool -> void {
        for k in 0..cn.argCount {
            ae: Expr = a.expr(a.argAt(cn, k));
            if (ae.op != Op.AddressOf) { continue; }
            x: Sym = NO_SYM;
            match ae.payload { Sub(v) { x = self.convBareName(a, v); } _ { } }
            if (x == NO_SYM) { continue; }
            isScalar: bool = false;
            for i in 0..names.len() { if (names.get(i) == x && scalar.get(i)) { isScalar = true; } }
            if (!isScalar) { continue; }
            at: long = self.fnNodeOf(cn.name);
            base: long = 0;
            if (cn.receiver != NO_NODE) { base = 1; }
            lend: bool = !inUnsafe;
            if (at >= 0 && base + k < a.fns.get(at).argCount) {
                pd: VarDeclNode = a.paramAt(a.fns.get(at), base + k);
                lend = pd.conv == Conv.Inout && pd.kind == Lit.Ref && isInoutScalarName(pd.structName);
            }
            if (lend) {
                self.bmWholeWrite(a, x, names, scalar, stores, held, armAt,
                                  keepString(format("\nnote: it is lent to `{}`, which may assign it through its `inout` parameter", nameOf(cn.name))));
            }
        }
    }

    // The same for a name a destructure bound, `x`: an element of a tuple, which is written where the
    // tuple lies.
    bmWholeElement &self inout a:Ast x:Sym inout names:Vec<Sym> inout stores:Vec<NodeId> inout held:Vec<Sym> note:str -> void {
        elem: str = "";
        for i in 0..names.len() {
            if (names.get(i) != x) { continue; }
            match a.expr(a.expr(stores.get(i)).right).payload {
                Field(f) { elem = fieldSpelling(a.fields.get(f).name); }
                _ { }
            }
        }
        if (held.len() == 0 || charAt(nameOf(held.get(0)), 0) == '$') {
            failStr(format("cannot assign to `{}`, a borrow of an element of the destructured tuple{}\nhelp: assign the element where the tuple lies, or replace the whole tuple",
                           nameOf(x), note));
        }
        place: String;
        for k in 0..held.len() {
            c: str = nameOf(held.get(k));
            if (k > 0 && !strStartsWith(c, "[")) { place.push('.'); }
            place.pushStr(c);
        }
        failStr(format("cannot assign to `{}`, a borrow of an element of `{}`{}\nhelp: assign the element itself, `{}.{} = ...`, or replace the whole tuple",
                       nameOf(x), place, note, place, elem));
    }

    // The refusal of a write to binding `x` as a whole. `note` is a line saying how, or "".
    bmWholeWrite &self inout a:Ast x:Sym inout names:Vec<Sym> inout scalar:Vec<bool> inout stores:Vec<NodeId>
                 inout held:Vec<Sym> armAt:long note:str -> void {
        isScalar: bool = false;
        for i in 0..names.len() { if (names.get(i) == x) { isScalar = scalar.get(i); } }
        if (armAt < 0) { self.bmWholeElement(a, x, names, stores, held, note); }
        what: str = "assign to its fields, or replace the variant";
        if (isScalar) { what = "replace the variant instead"; }
        // The variant as a constructor of its enum, the enum as the first binding's store reads it.
        enumName: Sym = NO_SYM;
        match a.expr(a.expr(stores.get(0)).right).payload {
            Field(f) { enumName = a.expr(a.fields.get(f).base).structName; }
            _ { }
        }
        ctor: String = format("{}.{}(...)", self.spellType(Lit.Struct, enumName), variantSpelling(a.arms.get(armAt).variant));
        // The matched value as the source names it, when it is a place the source names.
        if (held.len() == 0 || charAt(nameOf(held.get(0)), 0) == '$') {
            failStr(format("cannot assign to `{}`, a borrow of the matched value's payload{}\nhelp: {} where the value lies, with `{}`",
                           nameOf(x), note, what, ctor));
        }
        place: String;
        for k in 0..held.len() {
            c: str = nameOf(held.get(k));
            if (k > 0 && !strStartsWith(c, "[")) { place.push('.'); }
            place.pushStr(c);
        }
        failStr(format("cannot assign to `{}`, a borrow of the payload of `{}`{}\nhelp: {}: `{} = {}`",
                       nameOf(x), place, note, what, place, ctor));
    }

    // An owned subject: an arm that binds an owning payload takes the value apart, and the
    // subject's flag then says it releases nothing. A slot the arm discards with `_` would be
    // released by nobody, so it is bound to a hidden local of its own, released at the arm's end.
    bmTakeRest &self inout a:Ast armAt:long -> void {
        arm: ArmNode = a.arms.get(armAt);
        // The owning bindings' stores name the subject and its type.
        base: Expr = Expr { op: Op.Lvalue, left: NO_NODE, right: NO_NODE, kind: Lit.Void,
                            structName: NO_SYM, isParen: false, payload: Payload.None };
        found: bool = false;
        discards: long = 0;
        for i in 0..arm.bindCount {
            nm: Sym = a.names.get(arm.firstBind + i);
            if (nameOf(nm) == "_") { discards = discards + 1; continue; }
            if (found) { continue; }
            s: long = self.bmOwningBinding(a, arm.body, nm);
            if (s < 0) { continue; }
            rhs: Expr = a.expr(a.expr(a.exprStmts.get(a.stmtAt(arm.body, s + 1).at).value).right);
            p: Payload = rhs.payload;
            match p { Field(f) { base = a.expr(a.fields.get(f).base); found = true; } _ { } }
        }
        if (!found || discards == 0) { return; }
        sd: long = gReg.findStructSym(base.structName);
        if (sd < 0) { return; }
        def: StructDef = gReg.structDef(sd);
        ids: Vec<long>;
        for i in 0..arm.bindCount {
            nm: Sym = a.names.get(arm.firstBind + i);
            slot: Sym = enumPayloadField(nameOf(arm.variant), i);
            if (nameOf(nm) != "_") { continue; }
            fi: long = gReg.findFieldSym(def, slot);
            if (fi < 0) { continue; }
            fd: FieldDef = gReg.fieldAt(def, fi);
            if (fd.kind != Lit.Struct || !gReg.needsDrop(fd.structName)) { continue; }
            t: Sym = internString(format("$rest{}", self.ownSeq));
            self.ownSeq = self.ownSeq + 1;
            a.decls.push(VarDeclNode { name: t, kind: Lit.Struct, structName: fd.structName,
                                       isArray: false, count: 0, conv: Conv.None,
                                       isVariadic: false, elemKind: Lit.Void,
                                       elemStruct: NO_SYM, init: NO_NODE });
            ids.push(a.addStmt(StmtKind.VarDecl, a.decls.len() - 1));
            b: NodeId = a.addExpr(base);
            a.fields.push(FieldNode { base: b, name: slot });
            rhs: NodeId = a.leafOf(Op.FieldAccess, Payload.Field(a.fields.len() - 1),
                                   Lit.Struct, fd.structName);
            lhs: NodeId = a.leafOf(Op.Lvalue, Payload.Name(t), Lit.Struct, fd.structName);
            a.exprStmts.push(ExprStmtNode { value: a.binary(Op.Assignment, lhs, rhs, Lit.Struct) });
            ids.push(a.addStmt(StmtKind.Expr, a.exprStmts.len() - 1));
        }
        if (ids.len() == 0) { return; }
        n: long = a.blockLen(arm.body);
        for k in 0..n { ids.push(a.stmtIdAt(arm.body, k)); }
        arm.body = a.addBlock(ids);
        a.arms.set(armAt, arm);
    }

    // Where binding `nm`'s declaration sits in the arm's prologue (its store is the statement
    // after it), when its payload owns something; -1 otherwise.
    bmOwningBinding &self inout a:Ast body:long nm:Sym -> long {
        s: long = bindingAt(a, body, nm);
        if (s < 0) { return -1; }
        d: VarDeclNode = a.decls.get(a.stmtAt(body, s).at);
        if (d.kind != Lit.Struct || !gReg.needsDrop(d.structName)) { return -1; }
        return s;
    }

    // `a, b = t;` where `t` is borrowed (a match binding through a borrow, a field of `&self`, a
    // global): the destructure (`$tupN: T; $tupN = t; a: A; a = $tupN.$0; ...`, at `k` in `b`)
    // binds borrows, as the match does, and moves nothing out. The hidden local becomes a borrow of
    // `t`, and each name whose element owns something a borrow of that element. Where a write
    // through a name lands in a value this function does not own (`bmLending`), the names follow
    // the match's rule for a payload that owns nothing (`bmPlainBinds`): none is assigned as a
    // whole, and one of a struct is a borrow of its element where the code after it writes through
    // it, which the guard decides (`gCopyBinds`), so a tuple that owns nothing is a copy until then.
    bmDestructure &self inout a:Ast b:long k:long fnAt:long -> void {
        n: long = a.blockLen(b);
        if (k + 1 >= n || a.stmtAt(b, k + 1).kind != StmtKind.Expr) { return; }
        d: VarDeclNode = a.decls.get(a.stmtAt(b, k).at);
        if (d.kind != Lit.Struct) { return; }
        asn: NodeId = a.exprStmts.get(a.stmtAt(b, k + 1).at).value;
        ae: Expr = a.expr(asn);
        if (ae.op != Op.Assignment) { return; }
        src: Expr = a.expr(ae.right);
        root: Sym = self.ownPlaceRoot(a, ae.right);
        viaRef: bool = src.kind == Lit.Ref;
        owning: bool = gReg.needsDrop(d.structName);
        borrowed: bool = viaRef || (root != NO_SYM && self.bmIsBorrow(root));
        lending: bool = viaRef || (root != NO_SYM && self.bmLending(root));
        // An owning tuple's names are borrows wherever it is borrowed; one that owns nothing has
        // only copies to decide on, and only where a write through them would land elsewhere: a
        // place (a borrow a call returned of a tuple that owns nothing is a copy safe code cannot
        // name the place of).
        if ((owning && !borrowed) || (!owning && !lending)) { return; }
        // The place the names are borrows into, which the code after them may not write; for a
        // borrow a call returned (`v.at(i)`), all of what the call was lent (`v`).
        held: Vec<Sym>;
        self.xPath.clear();
        if (self.pathOf(a, ae.right) > 0 || (viaRef && self.lentByCall(a, ae.right) > 0)) { held.extend(self.xPath); }
        parent: long = -1;
        if (owning) {
            if (viaRef) {
                // Already a borrow: the hidden local is the same pointer.
                asRef: VarDeclNode = d;
                asRef.kind = Lit.Ref;
                asRef.isArray = false;
                asRef.count = 0;
                asRef.isVariadic = false;
                a.decls.set(a.stmtAt(b, k).at, asRef);
                ae.kind = Lit.Ref;
                ae.structName = d.structName;
                a.setExpr(asn, ae);
            } else { borrowRetype(a, a.stmtAt(b, k).at, asn); }
            restampFrom(a, b, k, d.name);
            self.bmLocals.put(nameOf(d.name), true);
        } else {
            // A tuple that owns nothing, read into a copy: a borrow of the place once a name read
            // out of it is one.
            gCopyBinds.push(CopyBind { name: d.name, decl: a.stmtAt(b, k).at, store: asn, body: b, subject: true,
                                       viaRef: viaRef, parent: self.bmCopyOf(root), fnName: a.fns.get(fnAt).name,
                                       conflict: "", conflictPos: 0 });
            parent = gCopyBinds.len() - 1;
            self.bmCopies.put(nameOf(d.name), parent);
        }
        // The names: a declaration and its store each, reading `$tupN.$j`. Each owning one is
        // restamped from its own declaration on, not from the block's start: a block before it may
        // have declared a value of the same name (`{ a: Res = ...; }` then `a, b = self.p;`), which
        // the parser gives the same name, and that value is not a borrow.
        names: Vec<Sym>;
        scalar: Vec<bool>;
        decls: Vec<long>;
        stores: Vec<NodeId>;
        made: Vec<Sym>;           // the owning names, borrows already
        madeStores: Vec<NodeId>;
        j: long = k + 2;
        while (j + 1 < n && a.stmtAt(b, j).kind == StmtKind.VarDecl && a.stmtAt(b, j + 1).kind == StmtKind.Expr) {
            nd: VarDeclNode = a.decls.get(a.stmtAt(b, j).at);
            na: NodeId = a.exprStmts.get(a.stmtAt(b, j + 1).at).value;
            ne: Expr = a.expr(na);
            if (ne.op != Op.Assignment || self.ownPlaceRoot(a, ne.right) != d.name) { break; }
            if (nd.kind == Lit.Struct && gReg.needsDrop(nd.structName)) {
                borrowRetype(a, a.stmtAt(b, j).at, na);
                restampFrom(a, b, j, nd.name);
                self.bmLocals.put(nameOf(nd.name), true);
                made.push(nd.name);
                madeStores.push(na);
            }
            names.push(nd.name);
            scalar.push(nd.kind != Lit.Struct || nd.isArray || namedScalar(nd.kind, nd.structName));
            decls.push(a.stmtAt(b, j).at);
            stores.push(na);
            j = j + 2;
        }
        // `_`'s blocks after them: through a borrow there is nothing to release, so each takes a
        // borrow of its element instead of the element.
        while (owning && j < n && a.stmtAt(b, j).kind == StmtKind.Block) {
            ib: long = a.blockStmts.get(a.stmtAt(b, j).at).body;
            if (a.blockLen(ib) != 2 || a.stmtAt(ib, 0).kind != StmtKind.VarDecl) { break; }
            dd: VarDeclNode = a.decls.get(a.stmtAt(ib, 0).at);
            if (!strStartsWith(nameOf(dd.name), "$discT")) { break; }
            borrowRetype(a, a.stmtAt(ib, 0).at, a.exprStmts.get(a.stmtAt(ib, 1).at).value);
            restampBlock(a, ib, dd.name);
            j = j + 1;
        }
        fnName: Sym = a.fns.get(fnAt).name;
        pos: long = gPos;
        // No name assigned as a whole, owning or not.
        if (lending && names.len() > 0) {
            self.bmCopyWalk(a, b, k + 2, &names, &scalar, &stores, &held, -1, false);
            gPos = pos;
        }
        // While an owning name is a borrow of its element, the code after it may not write the
        // tuple any other way, which could release the element under it: the match's rule for an
        // arm (`bmArmBlock`), from the names on.
        if (made.len() > 0) {
            self.bmDestr = true;
            self.bmArmFrom(a, b, k + 2, &held, &made, &madeStores, fnAt);
            self.bmDestr = false;
            self.bmHoldGlobal(&held, b, pos, fnAt, made.get(0), -1, fnName, true);
            gPos = pos;
        }
        if (!lending || names.len() == 0) { return; }
        // Each struct name that owns nothing noted.
        for i in 0..names.len() {
            nd: VarDeclNode = a.decls.get(decls.get(i));
            if (scalar.get(i) || gReg.needsDrop(nd.structName)) { continue; }
            gCopyBinds.push(CopyBind { name: names.get(i), decl: decls.get(i), store: stores.get(i), body: b,
                                       subject: false, viaRef: false, parent: parent, fnName: fnName,
                                       conflict: "", conflictPos: 0 });
            ci: long = gCopyBinds.len() - 1;
            self.bmCopies.put(nameOf(names.get(i)), ci);
            one: Vec<Sym>;
            one.push(names.get(i));
            from: long = declIndex(a, b, decls.get(i));
            self.bmDry = ci;
            self.bmDestr = true;
            self.bmArmFrom(a, b, from, &held, &one, &stores, fnAt);
            self.bmDestr = false;
            self.bmDry = -1;
            self.bmHoldGlobal(&held, b, pos, fnAt, names.get(i), ci, fnName, true);
        }
        gPos = pos;
    }

    // What a borrow call `id` returned is lent from, appended to `xPath`: its receiver's place, or
    // its first argument's that has one (`v` for `v.at(i)`), the whole of it, since an element of
    // what it holds may be anywhere in it. The answer is how many components were appended.
    lentByCall &self inout a:Ast id:NodeId -> long {
        e: Expr = a.expr(id);
        if (e.op != Op.FunctionCall && e.op != Op.MethodCall) { return 0; }
        match e.payload {
            Call(c) {
                cn: CallNode = a.calls.get(c);
                n: long = self.pathOf(a, cn.receiver);
                if (n > 0) { return n; }
                for k in 0..cn.argCount {
                    n = self.pathOf(a, a.argAt(cn, k));
                    if (n > 0) { return n; }
                }
            }
            _ { }
        }
        return 0;
    }

    // While an arm holds a borrow of the matched value's payload, the arm may write that payload
    // through the borrow and may not write the matched value any other way: an assignment to
    // it, or lending it mutably (an `inout` argument, a `&self` receiver), could release the
    // payload the borrow points at. The law of exclusivity, held for the arm rather than one call.
    bmArmBlock &self inout a:Ast b:long inout held:Vec<Sym> inout made:Vec<Sym> inout stores:Vec<NodeId> fnAt:long -> void {
        self.bmArmFrom(a, b, 0, held, made, stores, fnAt);
    }
    // The same from statement `from` of block `b` on: what follows a destructure's names.
    bmArmFrom &self inout a:Ast b:long from:long inout held:Vec<Sym> inout made:Vec<Sym> inout stores:Vec<NodeId> fnAt:long -> void {
        if (b < 0 || from < 0) { return; }
        n: long = a.blockLen(b);
        for k in from..n {
            a.enterStmt(a.stmtIdAt(b, k));
            st: Stmt = a.stmtAt(b, k);
            if (st.kind == StmtKind.VarDecl) { self.bmArmExpr(a, a.decls.get(st.at).init, held, made, stores, fnAt); }
            else if (st.kind == StmtKind.Expr || st.kind == StmtKind.Call) {
                self.bmArmExpr(a, a.exprStmts.get(st.at).value, held, made, stores, fnAt);
            }
            else if (st.kind == StmtKind.Return) { self.bmArmExpr(a, a.returns.get(st.at).value, held, made, stores, fnAt); }
            else if (st.kind == StmtKind.If) {
                c: long = st.at;
                while (c >= 0) {
                    nd: IfNode = a.ifs.get(c);
                    self.bmArmExpr(a, nd.cond, held, made, stores, fnAt);
                    self.bmArmBlock(a, nd.body, held, made, stores, fnAt);
                    c = nd.elseIf;
                }
            } else if (st.kind == StmtKind.While || st.kind == StmtKind.Recover) {
                w: WhileNode = a.whiles.get(st.at);
                self.bmArmExpr(a, w.cond, held, made, stores, fnAt);
                self.bmArmBlock(a, w.body, held, made, stores, fnAt);
                if (w.step >= 0) { self.bmArmBlock(a, w.step, held, made, stores, fnAt); }
            } else if (st.kind == StmtKind.Loop || st.kind == StmtKind.Unsafe || st.kind == StmtKind.Block) {
                self.bmArmBlock(a, a.blockStmts.get(st.at).body, held, made, stores, fnAt);
            } else if (st.kind == StmtKind.With) {
                w2: WithNode = a.withs.get(st.at);
                if (self.bmHeldRoot(w2.name, held)) { self.bmWritten(a, nameOf(w2.name), made, fnAt, "use `with` on"); }
                self.bmArmBlock(a, w2.body, held, made, stores, fnAt);
            } else if (st.kind == StmtKind.Match) {
                m: MatchNode = a.matches.get(st.at);
                for i in 0..m.armCount {
                    arm: ArmNode = a.arms.get(m.firstArm + i);
                    self.bmArmExpr(a, arm.test, held, made, stores, fnAt);
                    self.bmArmBlock(a, arm.body, held, made, stores, fnAt);
                }
            } else if (st.kind == StmtKind.Destructure) {
                self.bmArmExpr(a, a.destructures.get(st.at).value, held, made, stores, fnAt);
            }
        }
    }

    bmArmExpr &self inout a:Ast id:NodeId inout held:Vec<Sym> inout made:Vec<Sym> inout stores:Vec<NodeId> fnAt:long -> void {
        if (id == NO_NODE) { return; }
        e: Expr = a.expr(id);
        if (e.op == Op.Assignment && !nodeIn(stores, id)) {
            x: Sym = self.convBareName(a, e.left);
            // (A copy's whole stores were refused already, by `bmCopyWalk`.)
            if (x != NO_SYM && symIn(made, x) && self.bmDry < 0) {
                if (self.bmDestr) {
                    failStr(format("cannot assign to `{}`\nnote: it is a borrow of an element of the destructured tuple\nhelp: assign to its fields, or call a method on it",
                                   nameOf(x)));
                }
                failStr(format("cannot assign to `{}`\nnote: it is a borrow of the matched value's payload\nhelp: assign to its fields, or call a method on it",
                               nameOf(x)));
            }
            if (self.bmOverlaps(a, e.left, held)) { self.bmWritten(a, self.bmPathText(), made, fnAt, "assign to"); }
        }
        self.bmArmExpr(a, e.left, held, made, stores, fnAt);
        self.bmArmExpr(a, e.right, held, made, stores, fnAt);
        p: Payload = e.payload;
        match p {
            Sub(v)   { self.bmArmExpr(a, v, held, made, stores, fnAt); }
            Field(f) { self.bmArmExpr(a, a.fields.get(f).base, held, made, stores, fnAt); }
            Index(i) {
                ix: IndexNode = a.indexes.get(i);
                self.bmArmExpr(a, ix.base, held, made, stores, fnAt);
                self.bmArmExpr(a, ix.index, held, made, stores, fnAt);
                self.bmArmExpr(a, ix.sliceStart, held, made, stores, fnAt);
                self.bmArmExpr(a, ix.sliceEnd, held, made, stores, fnAt);
            }
            Call(c) {
                cn: CallNode = a.calls.get(c);
                at: long = self.fnNodeOf(cn.name);
                base: long = 0;
                if (cn.receiver != NO_NODE) {
                    base = 1;
                    self.bmArmArg(a, at, -1, cn.receiver, held, made, fnAt);
                    self.bmArmExpr(a, cn.receiver, held, made, stores, fnAt);
                }
                self.bmArmExpr(a, cn.callee, held, made, stores, fnAt);
                for k in 0..cn.argCount {
                    arg: NodeId = a.argAt(cn, k);
                    self.bmArmArg(a, at, base + k, arg, held, made, fnAt);
                    self.bmArmExpr(a, arg, held, made, stores, fnAt);
                }
            }
            Lit(l) {
                ln: LitNode = a.lits.get(l);
                self.bmArmExpr(a, ln.rest, held, made, stores, fnAt);
                for k in 0..ln.initCount {
                    self.bmArmExpr(a, a.inits.get(ln.firstInit + k).value, held, made, stores, fnAt);
                }
            }
            _ { }
        }
    }

    // An argument lent mutably: an `inout` parameter or a trait object, as the per-call law has it.
    // `i` is -1 for the receiver. A `&self` receiver is lent mutably only if the method writes
    // `self`, which the guard's write masks decide once every body is settled: the call is noted
    // here (`gSelfLends`) and refused there if it does. Deciding it here would refuse `e.clone()`
    // in an arm holding `e`'s payload, with `e` a read-only parameter, as a mutable lend.
    bmArmArg &self inout a:Ast at:long i:long arg:NodeId inout held:Vec<Sym> inout made:Vec<Sym> fnAt:long -> void {
        if (at < 0) { return; }
        f: FnNode = a.fns.get(at);
        pi: long = i;
        if (pi < 0) { pi = 0; }
        if (pi >= f.argCount) { return; }
        p: VarDeclNode = a.paramAt(f, pi);
        if (p.conv != Conv.Inout && p.kind != Lit.TraitObj) { return; }
        if (!self.bmOverlaps(a, arg, held)) { return; }
        if (i < 0 && p.kind == Lit.Ref && p.conv == Conv.Inout) {
            gSelfLends.push(SelfLend { callee: at, pos: gPos, fnName: a.fns.get(fnAt).name,
                                       what: self.bmPathText(), made: made.get(0), copy: self.bmDry, destr: self.bmDestr });
            return;
        }
        self.bmWritten(a, self.bmPathText(), made, fnAt, "mutably lend");
    }

    bmHeldRoot &self n:Sym inout held:Vec<Sym> -> bool {
        return held.len() > 0 && held.get(0) == n;
    }

    // Does the place `id` names overlap the held path? Leaves the place's path in `xPath`.
    bmOverlaps &self inout a:Ast id:NodeId inout held:Vec<Sym> -> bool {
        self.xPath.clear();
        n: long = self.pathOf(a, id);
        if (n == 0 || held.len() == 0) { return false; }
        m: long = n;
        if (held.len() < m) { m = held.len(); }
        for k in 0..m {
            if (!self.compsOverlap(self.xPath.get(k), held.get(k))) { return false; }
        }
        return true;
    }

    bmPathText &self -> str {
        return self.pathText(Access { first: 0, count: self.xPath.len(), writes: true });
    }

    // `how` is the verb: "assign to", "mutably lend", "use `with` on". For a copy the guard may
    // make a borrow (`bmDry`), what would be refused is kept with it, said where it stands.
    bmWritten &self inout a:Ast what:str inout made:Vec<Sym> fnAt:long how:str -> void {
        if (self.bmDry >= 0) {
            c: CopyBind = gCopyBinds.get(self.bmDry);
            if (c.conflict.len > 0) { return; }
            if (self.bmDestr) {
                c.conflict = keepString(format("cannot {} `{}` while `{}` borrows an element of it\nnote: the code after `{}` writes through it, which makes it a borrow of the element where it lies, and this write could replace the element under it\nhelp: finish with the borrow first, or destructure a clone",
                                               how, what, nameOf(made.get(0)), nameOf(made.get(0))));
            } else {
                c.conflict = keepString(format("cannot {} `{}` while a match arm borrows `{}`\nnote: the arm writes through `{}`, which makes it a borrow of the matched value's payload, and this write could replace the payload under it\nhelp: finish with the borrow first, or match on a clone",
                                               how, what, nameOf(made.get(0)), nameOf(made.get(0))));
            }
            c.conflictPos = gPos;
            gCopyBinds.set(self.bmDry, c);
            return;
        }
        if (self.bmDestr) {
            failStr(format("cannot {} `{}` while `{}` borrows an element of it\nnote: `{}` is a borrow of the element where it lies, and the write could release what it points at\nhelp: finish with the borrow first, or destructure a clone",
                           how, what, nameOf(made.get(0)), nameOf(made.get(0))));
        }
        failStr(format("cannot {} `{}` while a match arm borrows `{}`\nnote: `{}` is a borrow of the matched value's payload, and the write could release what it points at\nhelp: finish with the borrow first, or match on a clone",
                       how, what, nameOf(made.get(0)), nameOf(made.get(0))));
    }

    // ─── the moved set ───────────────────────────────────────────────────────
    // A handful of names per function, snapshotted at every branch and every loop entry. A
    // vector is the right shape for that: the whole set is copied far more often than it is
    // searched, and a map would cost an allocation per branch to save nothing.

    ownIsMoved &self n:Sym -> bool {
        for k in 0..self.moved.len() {
            if (self.moved.get(k) == n) { return true; }
        }
        return false;
    }
    ownUnmark &self n:Sym -> void {
        for k in 0..self.moved.len() {
            if (self.moved.get(k) == n) { self.moved.removeAt(k); return; }
        }
    }

    // ─── synthesized nodes ───────────────────────────────────────────────────

    // `__moved_<name>`: the hidden flag saying whether the value is still this scope's to
    // release. Spelled in one place so every site that reads or writes it agrees.
    ownFlagName &self n:Sym -> Sym {
        return internString(format("__moved_{}", nameOf(n)));
    }

    // `__moved_<name>: int; __moved_<name> = <initial>;`
    //
    // The flag means "nothing to drop": 1 for a declaration with no value yet, so that the
    // first store has nothing to release and needs no flow analysis to know it; 0 for anything
    // that arrives owning, a parameter, or a declaration with an initializer.
    ownFlagDecl &self inout a:Ast inout out:Vec<long> n:Sym initial:long -> void {
        a.decls.push(VarDeclNode { name: self.ownFlagName(n), kind: Lit.Int, structName: NO_SYM,
                                   isArray: false, count: 0, conv: Conv.None, isVariadic: false,
                                   elemKind: Lit.Void, elemStruct: NO_SYM, init: NO_NODE });
        out.push(a.addStmt(StmtKind.VarDecl, a.decls.len() - 1));
        self.ownSetFlag(a, out, n, initial);
    }

    ownSetFlag &self inout a:Ast inout out:Vec<long> n:Sym v:long -> void {
        lhs: NodeId = a.leafOf(Op.Lvalue, Payload.Name(self.ownFlagName(n)), Lit.Int, NO_SYM);
        rhs: NodeId = a.leaf(Op.Literal, Payload.Num(v), Lit.Int);
        a.exprStmts.push(ExprStmtNode { value: a.binary(Op.Assignment, lhs, rhs, Lit.Int) });
        out.push(a.addStmt(StmtKind.Expr, a.exprStmts.len() - 1));
    }

    // `<var>.drop()`, already resolved: this pass runs after typing, so nothing re-checks it.
    ownDropStmt &self inout a:Ast n:Sym sn:Sym -> long {
        recv: NodeId = a.leafOf(Op.Lvalue, Payload.Name(n), Lit.Struct, sn);
        return self.ownDropOf(a, recv, sn);
    }

    // The same for a place that is not a bare name: a field, an element.
    ownDropOf &self inout a:Ast recv:NodeId sn:Sym -> long {
        a.calls.push(CallNode { name: methodSymbol(sn, intern("drop")), receiver: recv,
                                firstArg: 0, argCount: 0, slot: NO_SLOT, callee: NO_NODE, sigKey: NO_SYM });
        call: NodeId = a.leafOf(Op.MethodCall, Payload.Call(a.calls.len() - 1), Lit.Void, NO_SYM);
        a.exprStmts.push(ExprStmtNode { value: call });
        return a.addStmt(StmtKind.Expr, a.exprStmts.len() - 1);
    }

    // `if (__moved_<flagVar> == 0) { <dropVar>.drop(); }`. The two names differ when what is
    // released is a saved copy of a value whose owner's flag says whether it was live.
    ownGuardedDrop &self inout a:Ast flagVar:Sym dropVar:Sym sn:Sym -> long {
        f: NodeId = a.leafOf(Op.Lvalue, Payload.Name(self.ownFlagName(flagVar)), Lit.Int, NO_SYM);
        z: NodeId = a.leaf(Op.Literal, Payload.Num(0), Lit.Int);
        body: Vec<long>;
        body.push(self.ownDropStmt(a, dropVar, sn));
        a.ifs.push(IfNode { cond: a.binary(Op.IsEqual, f, z, Lit.Int),
                            body: a.addBlock(body), elseIf: -1 });
        return a.addStmt(StmtKind.If, a.ifs.len() - 1);
    }

    // `if (__moved_<n> == 0) { <body> }`: what runs only while `n` still owns its value.
    ownIfOwns &self inout a:Ast n:Sym body:Vec<long> -> long {
        f: NodeId = a.leafOf(Op.Lvalue, Payload.Name(self.ownFlagName(n)), Lit.Int, NO_SYM);
        z: NodeId = a.leaf(Op.Literal, Payload.Num(0), Lit.Int);
        a.ifs.push(IfNode { cond: a.binary(Op.IsEqual, f, z, Lit.Int), body: a.addBlock(body), elseIf: -1 });
        return a.addStmt(StmtKind.If, a.ifs.len() - 1);
    }

    // ─── whole arrays of a Drop type ─────────────────────────────────────────
    //
    // A fixed array whose elements own something is a value like a struct that does: stored
    // whole it is MOVED. Its elements' bytes are copied, the destination's old elements released
    // first, and the source becomes moved-from: its flag set, so its scope exit releases nothing,
    // and any later read of it refused as a read of any moved value. Only a local array has a
    // flag, so only a local array is a source; a field, an element, a global or a borrow is not
    // (a partial move of an array field, or of one element, has nothing to record it on).

    // The length of the whole array `id` names (a local, a global, a field), or -1.
    ownWholeArray &self inout a:Ast id:NodeId -> long {
        if (id == NO_NODE) { return -1; }
        e: Expr = a.expr(id);
        match e.payload {
            Name(n) {
                if (e.op != Op.Lvalue) { return -1; }
                c: long = self.ownArrayCount(n);
                if (c > 0) { return c; }
                gi: long = gReg.findGlobalSym(n);
                if (gi >= 0 && gReg.globalDef(gi).isArray) { return gReg.globalDef(gi).count; }
            }
            Field(f) {
                if (e.op != Op.FieldAccess) { return -1; }
                fd: FieldNode = a.fields.get(f);
                be: Expr = a.expr(fd.base);
                if (be.kind != Lit.Struct && be.kind != Lit.Ref) { return -1; }
                si: long = gReg.findStructSym(be.structName);
                if (si < 0) { return -1; }
                d: StructDef = gReg.structDef(si);
                fi: long = gReg.findFieldSym(d, fd.name);
                if (fi < 0) { return -1; }
                fdef: FieldDef = gReg.fieldAt(d, fi);
                if (fdef.isArray) { return fdef.count; }
            }
            _ { }
        }
        return -1;
    }

    // A local array this function tracks: its length, or 0.
    ownArrayCount &self n:Sym -> long {
        k: long = self.scope.len();
        while (k > 0) {
            k = k - 1;
            v: OwnLocal = self.scope.get(k);
            if (v.name == n) { return v.count; }
        }
        return 0;
    }

    // The local array a whole-array store takes its elements from, refusing anything else.
    ownArraySource &self inout a:Ast src:NodeId -> Sym {
        e: Expr = a.expr(src);
        match e.payload {
            Name(n) { if (e.op == Op.Lvalue && self.ownArrayCount(n) > 0) { return n; } }
            _ { }
        }
        failStr(format("cannot move a whole array of `{}` out of {}\nnote: only a local array is moved whole, since its flag records the move\nhelp: move the elements one at a time (`take`, `replace`, `swapValues`), or clone them",
                       nameOf(e.structName), self.ownPlaceWords(a, src)));
    }
    // A place as a message names it: "the global `g`", "the field `f`", or "this place".
    ownPlaceWords &self inout a:Ast id:NodeId -> str {
        e: Expr = a.expr(id);
        match e.payload {
            Name(n) { if (gReg.findGlobalSym(n) >= 0) { return keepString(format("the global `{}`", lastComponentOf(nameOf(n)))); } }
            Field(f) { return keepString(format("the field `{}`", fieldSpelling(a.fields.get(f).name))); }
            _ { }
        }
        return "this place";
    }

    // `dst = src` of whole arrays of a Drop type: `dst`'s old elements released (a local's only
    // while it owns them, its flag says), the bytes copied by the statement itself, `dst` owning
    // again and `src` moved-from.
    ownArrayStore &self inout a:Ast inout out:Vec<long> e:Expr stmt:long -> void {
        sn: Sym = a.expr(e.left).structName;
        self.ownScanUses(a, e.right);
        src: Sym = self.ownArraySource(a, e.right);
        dst: Sym = NO_SYM;
        de: Expr = a.expr(e.left);
        match de.payload { Name(n) { if (de.op == Op.Lvalue && self.ownArrayCount(n) > 0) { dst = n; } } _ { } }
        if (dst == src) {
            failStr(format("cannot assign `{}` to itself\nnote: a whole array of `{}` is moved, and a move into its own source would release what it takes",
                           nameOf(src), nameOf(sn)));
        }
        count: long = self.ownWholeArray(a, e.left);
        body: Vec<long>;
        if (dst != NO_SYM) {
            self.elemLoop(a, &body, OwnLocal { name: dst, structName: sn, count: count }, NO_NODE, true);
            out.push(self.ownIfOwns(a, dst, body));
        } else {
            // A field of a value (`s.v = a`): released where it lies, and its owner must hold one.
            self.ownScanUses(a, e.left);
            if (self.ownPlaceRoot(a, e.left) == NO_SYM) {
                failStr(format("cannot move a whole array of `{}` into this place\nnote: such an array is moved only into a local array, or into a field of a value this function reaches by name",
                               nameOf(sn)));
            }
            self.elemLoop(a, &body, OwnLocal { name: NO_SYM, structName: sn, count: count }, e.left, true);
            out.extend(body);
        }
        out.push(stmt);
        if (dst != NO_SYM) {
            self.ownUnmark(dst);
            self.ownSetFlag(a, out, dst, 0);
        }
        self.ownMarkMoved(a, out, src);
    }

    // ─── scope exits ─────────────────────────────────────────────────────────

    // Everything one scope holds, released innermost value first: the reverse of the order it
    // was acquired in, so a value that was built from another is released before it.
    ownDropRange &self inout a:Ast inout out:Vec<long> from:long -> void {
        k: long = self.scope.len();
        while (k > from) {
            k = k - 1;
            self.ownRelease(a, out, self.scope.get(k));
        }
    }
    // One local's release, under its flag. Inside a `recover` body the flag is then set, so a
    // `raise` later in the body does not have the handler release it a second time.
    ownRelease &self inout a:Ast inout out:Vec<long> v:OwnLocal -> void {
        if (v.count > 0) {
            body: Vec<long>;
            self.elemLoop(a, &body, v, NO_NODE, true);
            out.push(self.ownIfOwns(a, v.name, body));
        }
        else if (self.hasPartial(v.name)) {
            out.push(self.ownPartialDrop(a, v.name, v.name, v.structName));
            // A loop may declare it again, with every field owned.
            self.ownPartialReset(a, out, v.name);
        }
        else { out.push(self.ownGuardedDrop(a, v.name, v.name, v.structName)); }
        if (self.ownRecover > 0) { self.ownSetFlag(a, out, v.name, 1); }
    }

    // Inside a `recover` body, the flag writes a statement's moves made (appended to `out` from
    // `from` on) go before the statement itself, which sits at `at`: if a callee in it takes a
    // value and then raises, the handler must not release that value again.
    ownMovesFirst &self inout out:Vec<long> at:long from:long -> void {
        if (self.ownRecover == 0 || from >= out.len()) { return; }
        moves: Vec<long>;
        for k in from..out.len() { moves.push(out.get(k)); }
        while (out.len() > from) { out.pop(); }
        for k in 0..moves.len() { out.insert(at + k, moves.get(k)); }
    }
    // The scope being closed.
    ownScopeDrops &self inout a:Ast inout out:Vec<long> -> void {
        self.ownDropRange(a, out, self.scopeBase.last());
    }
    // Every open scope, for a `return`: it leaves the function, not just this block.
    ownAllScopeDrops &self inout a:Ast inout out:Vec<long> -> void {
        self.ownDropRange(a, out, 0);
    }
    // What a `break` or a `continue` leaves: out to and including the loop body's own scope,
    // and no further, since (unlike after a `return`) the code after the loop still owns the rest.
    ownLoopDrops &self inout a:Ast inout out:Vec<long> -> void {
        if (self.loopBase.len() == 0) { return; }
        self.ownDropRange(a, out, self.loopBase.last());
    }

    // `k = <first>; while (k <op> <limit>) { arr[k]<step>; k = k + <by>; }`: an array of owning
    // elements is built and released as a whole. There is no per-element flag a move could set,
    // so every element is made at the declaration and every element released at scope exit, in
    // reverse index order; that is what makes releasing all N sound.
    // `v` names the array and its element type; `base` is the expression it hangs off when it
    // is a field rather than a local. The two travel as one value because six is all a call
    // takes.
    elemLoop &self inout a:Ast inout out:Vec<long> v:OwnLocal base:NodeId dropping:bool -> void {
        t: Sym = v.structName;
        // The base is an expression, never a bare name: `lowerElemAddress` reads its type to
        // decide whether to take an address or load a pointer, and a missing one indexes the
        // arena at -1. A local array's base is the lvalue naming it, typed as its element is.
        seq: NodeId = base;
        if (seq == NO_NODE) { seq = a.leafOf(Op.Lvalue, Payload.Name(v.name), Lit.Struct, t); }
        count: long = v.count;
        c: Sym = internString(format("__ae{}", self.ownSeq));
        self.ownSeq = self.ownSeq + 1;
        from: long = 0;
        by: long = 1;
        if (dropping) { from = count - 1; by = -1; }
        a.decls.push(VarDeclNode { name: c, kind: Lit.Long, structName: NO_SYM,
                                   isArray: false, count: 0, conv: Conv.None, isVariadic: false,
                                   elemKind: Lit.Void, elemStruct: NO_SYM,
                                   init: a.leaf(Op.Literal, Payload.Num(from), Lit.Long) });
        out.push(a.addStmt(StmtKind.VarDecl, a.decls.len() - 1));

        a.indexes.push(IndexNode { name: v.name, base: seq,
                                   index: a.leafOf(Op.Lvalue, Payload.Name(c), Lit.Long, NO_SYM),
                                   whole: false, rawPointerBase: false,
                                   sliceStart: NO_NODE, sliceEnd: NO_NODE, at: NO_SYM });
        elem: NodeId = a.leafOf(Op.ArrayIndex, Payload.Index(a.indexes.len() - 1), Lit.Struct, t);
        body: Vec<long>;
        if (dropping) { body.push(self.ownDropOf(a, elem, t)); }
        else {
            a.calls.push(CallNode { name: self.resolveFn(methodSymbol(t, intern("new"))),
                                    receiver: NO_NODE, firstArg: 0, argCount: 0,
                                    slot: NO_SLOT, callee: NO_NODE, sigKey: NO_SYM });
            made: NodeId = a.leafOf(Op.FunctionCall, Payload.Call(a.calls.len() - 1), Lit.Struct, t);
            a.exprStmts.push(ExprStmtNode { value: a.binary(Op.Assignment, elem, made, Lit.Struct) });
            body.push(a.addStmt(StmtKind.Expr, a.exprStmts.len() - 1));
        }
        cref: NodeId = a.leafOf(Op.Lvalue, Payload.Name(c), Lit.Long, NO_SYM);
        step: NodeId = a.binary(Op.Assignment,
                                a.leafOf(Op.Lvalue, Payload.Name(c), Lit.Long, NO_SYM),
                                a.binary(Op.Addition, cref,
                                         a.leaf(Op.Literal, Payload.Num(by), Lit.Long), Lit.Long),
                                Lit.Long);
        a.exprStmts.push(ExprStmtNode { value: step });
        body.push(a.addStmt(StmtKind.Expr, a.exprStmts.len() - 1));

        op: Op = Op.LessThan;
        limit: long = count;
        if (dropping) { op = Op.IsGreaterOrEqual; limit = 0; }
        cond: NodeId = a.binary(op, a.leafOf(Op.Lvalue, Payload.Name(c), Lit.Long, NO_SYM),
                                a.leaf(Op.Literal, Payload.Num(limit), Lit.Long), Lit.Int);
        a.whiles.push(WhileNode { cond: cond, body: a.addBlock(body), step: -1 });
        out.push(a.addStmt(StmtKind.While, a.whiles.len() - 1));
    }

    // ─── the walk ────────────────────────────────────────────────────────────

    ownFunction &self inout a:Ast at:long -> void {
        f: FnNode = a.fns.get(at);
        self.dropOf.clear(); self.dropDepth.clear(); self.fresh.clear(); self.ownParams.clear();
        self.scope.clear(); self.scopeBase.clear(); self.moved.clear();
        self.loopBase.clear(); self.loopMoved.clear(); self.loopMovedBase.clear();
        self.pmust.clear(); self.pmustLoop.clear(); self.pmustLoopBase.clear();
        self.pFlags.clear(); self.pHoles.clear(); self.pCond = 0;
        self.loopDepth = 0;
        self.ownRecover = 0;
        self.recLocals.clear(); self.recLocalsBase.clear(); self.recMoved.clear(); self.recMovedBase.clear();
        for k in 0..f.argCount {
            self.ownParams.put(nameOf(a.paramAt(f, k).name), true);
        }
        self.ownFn = at;
        self.ownSeeding = true;
        self.ownUnsafe = 0;
        if (f.isUnsafe) { self.ownUnsafe = 1; }
        self.addrFills.clear();
        self.ownBlock(a, f.body);
        if (self.pHoles.len() > 0) { self.ownFillHoles(a, f.body); }
    }

    // ─── partial moves ───────────────────────────────────────────────────────
    //
    // `s: Res = acc.s` takes one field out of an owned local and leaves the rest of it owned:
    // `acc.n` is still readable, `acc` as a whole and `acc.s` are not, and the scope exit releases
    // the owning fields still there, one by one, in place of `acc.drop()`. The move is an entry of
    // its own in `moved` (`acc.s`, a name no source can spell), and whether it happened on every
    // path walked so far is `pmust`. That is all a release needs to know when the move was made
    // unconditionally: the field is not released, and nothing at run time says so. Only a move made
    // on some paths and not others (in one arm of an `if`, say) needs a flag, `__moved_acc.s`,
    // and which ones do is known only where a release reads it, after the moves were written. So
    // each move (and each place the field becomes owned again) leaves an empty block where the
    // flag's store would go, and the walk's end fills in those whose entry got a flag, and declares
    // the flags, zeroed, at the top of the function. A move made unconditionally costs nothing.
    //
    // Refused: a partial move out of a type with a `drop` of its own (that `drop` must still run,
    // and it reads every field), out of a field of a field (`h.a.b`), and out of anything the
    // function does not own; using the whole value after one; reading the moved field.

    partialEntry &self owner:Sym field:Sym -> Sym {
        e: Sym = internString(format("{}.{}", nameOf(owner), nameOf(field)));
        if (!self.pOwner.has(nameOf(e))) {
            self.pOwner.put(nameOf(e), owner);
            self.pField.put(nameOf(e), field);
        }
        return e;
    }
    isPartial &self n:Sym -> bool { return self.pOwner.has(nameOf(n)); }
    partialOwner &self n:Sym -> Sym { return self.pOwner.get(nameOf(n)); }

    // Is some field of `owner` moved out on some path to here?
    hasPartial &self owner:Sym -> bool {
        for k in 0..self.moved.len() {
            m: Sym = self.moved.get(k);
            if (self.isPartial(m) && self.partialOwner(m) == owner) { return true; }
        }
        return false;
    }
    inMust &self n:Sym -> bool { return symIn(self.pmust, n); }
    dropMust &self n:Sym -> void {
        for k in 0..self.pmust.len() {
            if (self.pmust.get(k) == n) { self.pmust.removeAt(k); return; }
        }
    }

    // An empty block standing where `__moved_<entry> = value;` goes if the entry gets a flag.
    ownFlagHole &self inout a:Ast inout out:Vec<long> entry:Sym value:long -> void {
        none: Vec<long>;
        a.blockStmts.push(BlockStmtNode { body: a.addBlock(none) });
        self.pHoles.push(PHole { at: a.blockStmts.len() - 1, entry: entry, value: value });
        out.push(a.addStmt(StmtKind.Block, a.blockStmts.len() - 1));
    }

    // Every partial entry of `owner` on some path to here becomes owned again (a store of the
    // whole value, or the value's scope ending, after which a loop may declare it afresh).
    ownPartialReset &self inout a:Ast inout out:Vec<long> owner:Sym -> void {
        for k in 0..self.moved.len() {
            m: Sym = self.moved.get(k);
            if (self.isPartial(m) && self.partialOwner(m) == owner) { self.ownFlagHole(a, out, m, 0); }
        }
    }
    ownPartialForget &self owner:Sym -> void {
        k: long = 0;
        while (k < self.moved.len()) {
            m: Sym = self.moved.get(k);
            if (self.isPartial(m) && self.partialOwner(m) == owner) {
                self.moved.removeAt(k);
                self.dropMust(m);
            } else { k = k + 1; }
        }
    }

    // What `drop` of `owner`'s value would release, field by field, leaving out what was moved:
    // `if (__moved_<owner> == 0) { <each owning field still there>.drop(); }`, a field moved on
    // some paths only under its own flag. `dropVar` holds the value (the owner itself, or a saved
    // copy of what a store overwrites).
    ownPartialDrop &self inout a:Ast owner:Sym dropVar:Sym sn:Sym -> long {
        body: Vec<long>;
        si: long = gReg.findStructSym(sn);
        if (si >= 0) {
            d: StructDef = gReg.structDef(si);
            k: long = d.fieldCount;
            while (k > 0) {
                k = k - 1;
                f: FieldDef = gReg.fieldAt(d, k);
                if (!(f.kind == Lit.Struct && gReg.needsDrop(f.structName))) { continue; }
                e: Sym = self.partialEntry(owner, f.name);
                if (self.ownIsMoved(e) && self.inMust(e)) { continue; }
                recv: NodeId = a.leafOf(Op.Lvalue, Payload.Name(dropVar), Lit.Struct, sn);
                a.fields.push(FieldNode { base: recv, name: f.name });
                fv: NodeId = a.leafOf(Op.FieldAccess, Payload.Field(a.fields.len() - 1), Lit.Struct, f.structName);
                if (f.isArray) {
                    self.elemLoop(a, &body, OwnLocal { name: NO_SYM, structName: f.structName, count: f.count }, fv, true);
                    continue;
                }
                st: long = self.ownDropOf(a, fv, f.structName);
                if (self.ownIsMoved(e)) {
                    if (!symIn(self.pFlags, e)) { self.pFlags.push(e); }
                    st = self.ownFlagGuard(a, e, st);
                }
                body.push(st);
            }
        }
        return self.ownFlagGuard(a, owner, a.addStmt(StmtKind.Block, self.blockOf(a, body)));
    }

    // `if (__moved_<n> == 0) { <st> }`
    ownFlagGuard &self inout a:Ast n:Sym st:long -> long {
        f: NodeId = a.leafOf(Op.Lvalue, Payload.Name(self.ownFlagName(n)), Lit.Int, NO_SYM);
        z: NodeId = a.leaf(Op.Literal, Payload.Num(0), Lit.Int);
        body: Vec<long>;
        body.push(st);
        a.ifs.push(IfNode { cond: a.binary(Op.IsEqual, f, z, Lit.Int), body: a.addBlock(body), elseIf: -1 });
        return a.addStmt(StmtKind.If, a.ifs.len() - 1);
    }
    blockOf &self inout a:Ast ids:Vec<long> -> long {
        a.blockStmts.push(BlockStmtNode { body: a.addBlock(ids) });
        return a.blockStmts.len() - 1;
    }

    // The walk is done: every flag a release read is declared at the function's top, zeroed, and
    // every store to one written where its hole was left. A hole of an entry with no flag stays
    // empty, which is what an unconditional partial move costs.
    ownFillHoles &self inout a:Ast body:long -> void {
        for k in 0..self.pHoles.len() {
            h: PHole = self.pHoles.get(k);
            if (!symIn(self.pFlags, h.entry)) { continue; }
            ids: Vec<long>;
            self.ownSetFlag(a, &ids, h.entry, h.value);
            a.blockStmts.set(h.at, BlockStmtNode { body: a.addBlock(ids) });
        }
        if (self.pFlags.len() == 0) { return; }
        top: Vec<long>;
        for k in 0..self.pFlags.len() { self.ownFlagDecl(a, &top, self.pFlags.get(k), 0); }
        n: long = a.blockLen(body);
        for k in 0..n { top.push(a.stmtIdAt(body, k)); }
        first: long = a.stmtRuns.len();
        a.stmtRuns.extend(top);
        a.blocks.set(body, Block { firstStmt: first, stmtCount: top.len() });
    }

    // Rewrite one block: track the moves its statements make, and insert the flags and the
    // guarded releases. True when the block cannot fall out of its end, which is what tells the
    // caller not to append drops after it and not to merge what it moved.
    ownBlock &self inout a:Ast b:long -> bool {
        self.scopeBase.push(self.scope.len());
        out: Vec<long>;
        // A by-value Drop parameter is the callee's: the caller moved it in, so the callee is
        // what releases it. A borrow is not, and is skipped.
        if (self.ownSeeding) {
            self.ownSeeding = false;
            f: FnNode = a.fns.get(self.ownFn);
            for k in 0..f.argCount {
                p: VarDeclNode = a.paramAt(f, k);
                if (p.kind == Lit.Struct && !p.isArray && !p.isVariadic && p.conv != Conv.Read
                    && gReg.needsDrop(p.structName)) {
                    self.ownTrack(p.name, p.structName, 0);
                    self.ownFlagDecl(a, &out, p.name, 0);
                }
            }
        }
        diverged: bool = false;
        run: long = a.blocks.get(b).firstStmt;
        n: long = a.blockLen(b);
        for k in 0..n {
            id: long = a.stmtRuns.get(run + k);
            w: long = a.enterStmt(id);
            self.stmtMoves = 0;
            if (self.ownStmt(a, &out, a.stmts.get(id), id)) { diverged = true; }
            // A raw address taken of an owning local (`memcpy(&gone as long, p, n)`) is how trusted
            // code fills it, and it holds a value from here: released at its scope's end, as
            // definite initialization already counts the `&x` as its assignment. Otherwise one
            // declared without a value would keep its "nothing to release" flag and never be
            // dropped.
            if (self.addrFills.len() > 0) {
                if (!diverged) {
                    for j in 0..self.addrFills.len() { self.ownSetFlag(a, &out, self.addrFills.get(j), 0); }
                }
                self.addrFills.clear();
            }
            gPos = w;
        }
        if (!diverged) { self.ownScopeDrops(a, &out); }
        base: long = self.scopeBase.last();
        while (self.scope.len() > base) { self.scope.pop(); }
        self.scopeBase.pop();
        first: long = a.stmtRuns.len();
        a.stmtRuns.extend(out);
        a.blocks.set(b, Block { firstStmt: first, stmtCount: out.len() });
        return diverged;
    }

    ownTrack &self n:Sym sn:Sym count:long -> void {
        self.scope.push(OwnLocal { name: n, structName: sn, count: count });
        if (self.ownRecover > 0) { self.recLocals.push(OwnLocal { name: n, structName: sn, count: count }); }
        // An array's depth too: a whole-array move out of one declared outside a loop is refused
        // inside it (`ownRepeatingMove`), as any owning local's is.
        self.dropDepth.put(nameOf(n), self.loopDepth);
        if (count == 0) { self.dropOf.put(nameOf(n), sn); }
    }

    ownStmt &self inout a:Ast inout out:Vec<long> st:Stmt id:long -> bool {
        if (st.kind == StmtKind.VarDecl) {
            d: VarDeclNode = a.decls.get(st.at);
            self.ownScanUses(a, d.init);
            // A borrow stored into a borrow local copies nothing; anything else takes the value,
            // and a value taken from a place that cannot record the move is refused.
            if (d.kind != Lit.Ref) { self.ownRejectMove(a, d.init, "assigned to a local"); }
            temps: Vec<Sym>;
            self.ownHoistTemps(a, out, &temps, d.init, false);
            at: long = out.len();
            out.push(id);
            // Per declaration: the parser gives sibling declarations of one spelling one name, so
            // what a sibling scope moved (`e` handed on inside one loop body) says nothing about
            // this value, which arrives owning or unassigned. Otherwise the earlier move would stay
            // in the set, and `e: Vec<long>; rows.push(e);` in a later loop would be refused as a
            // use of a moved value. Nor is a sibling's type this one's: a `long` named like an
            // earlier owning value is not tracked (`ownTrack` below records this declaration when
            // it owns).
            self.ownUnmark(d.name);
            self.ownPartialForget(d.name);
            self.fresh.remove(nameOf(d.name));
            self.dropOf.remove(nameOf(d.name));
            self.dropDepth.remove(nameOf(d.name));
            if (d.kind == Lit.Struct && gReg.needsDrop(d.structName)) {
                if (d.isArray && d.count > 0 && d.init != NO_NODE && a.expr(d.init).op != Op.ArrayLit) {
                    // `b: [T; N] = a`: the declaration's copy took `a`'s elements, so `b` owns
                    // them and `a` is moved-from.
                    src: Sym = self.ownArraySource(a, d.init);
                    self.ownTrack(d.name, d.structName, d.count);
                    self.ownFlagDecl(a, out, d.name, 0);
                    self.ownMarkMoved(a, out, src);
                } else if (d.isArray) {
                    // No flag: an element cannot be moved out (there is no per-element flag to
                    // record it), so every element is live at scope exit by construction, which
                    // holds only because every element is built here. An element type without
                    // `Default` cannot be, so such an array is left alone rather than released.
                    if (d.count > 0 && d.init == NO_NODE
                        && gReg.structImplements(nameOf(d.structName), intern("Default"))
                        && self.fnNames.has(nameOf(methodSymbol(d.structName, intern("new"))))) {
                        self.elemLoop(a, out,
                                      OwnLocal { name: d.name, structName: d.structName,
                                                 count: d.count },
                                      NO_NODE, false);
                        self.ownTrack(d.name, d.structName, d.count);
                        // Its flag, as any owning local's: a whole-array move sets it.
                        self.ownFlagDecl(a, out, d.name, 0);
                    } else if (d.count > 0 && d.init == NO_NODE) {
                        // ...and leaving it alone silently is the one thing that must not happen:
                        // the array's elements would be released by nothing at all.
                        failStr(format("`{}` does not implement `Default`\nnote: the elements of the array `{}` own something, so every one of them is built up front and released at the end of its scope\nhelp: give it `methods {} for Default`",
                                       nameOf(d.structName), nameOf(d.name), nameOf(d.structName)));
                    }
                } else {
                    self.ownTrack(d.name, d.structName, 0);
                    if (d.init == NO_NODE) {
                        self.fresh.put(nameOf(d.name), true);
                        self.ownFlagDecl(a, out, d.name, 1);
                    } else {
                        self.ownFlagDecl(a, out, d.name, 0);
                    }
                }
            }
            mv: long = out.len();
            self.ownApplyMoves(a, out, a.decls.get(st.at).init);
            self.ownMovesFirst(out, at, mv);
            self.ownReleaseTemps(a, out, &temps);
            return false;
        }
        if (st.kind == StmtKind.Expr || st.kind == StmtKind.Call) {
            self.ownExprStmt(a, out, a.exprStmts.get(st.at).value, id);
            // A call to a `-> never` function ends the path, as a `return` does, but releases
            // nothing: the process ends there.
            return self.neverStmt(a, st);
        }
        if (st.kind == StmtKind.Return) {
            self.ownReturn(a, out, st.at, id);
            return true;
        }
        if (st.kind == StmtKind.If) {
            // Only the first condition is evaluated unconditionally, so only its temporaries can
            // be hoisted ahead of the statement (and are released after it); an `else if`'s is
            // reached on a path of its own (`ownIf`). What it moves is moved on every path.
            cond: NodeId = a.ifs.get(st.at).cond;
            temps: Vec<Sym>;
            self.ownScanUses(a, cond);
            self.ownHoistTemps(a, out, &temps, cond, true);
            self.ownApplyMoves(a, out, a.ifs.get(st.at).cond);
            self.ownIf(a, st.at, true);
            out.push(id);
            self.ownReleaseTemps(a, out, &temps);
            return false;
        }
        if (st.kind == StmtKind.While) {
            // A condition that builds an owning temporary, or moves, is evaluated each time round,
            // so it becomes the loop body's first statement: `while (true) { c: bool = <cond>;
            // if (!c) { break; } ... }`, where a declaration's own rules release the temporary.
            w0: WhileNode = a.whiles.get(st.at);
            if (self.ownCondNeeds(a, w0.cond, true)) {
                body: Vec<long>;
                t: Sym = self.ownCondDecl(a, &body, w0.cond);
                brk: Vec<long>;
                brk.push(a.addStmt(StmtKind.Break, 0));
                notC: NodeId = a.unary(Op.LogicalNot, a.leafOf(Op.Lvalue, Payload.Name(t), Lit.Bool, NO_SYM), Lit.Bool);
                a.ifs.push(IfNode { cond: notC, body: a.addBlock(brk), elseIf: -1 });
                body.push(a.addStmt(StmtKind.If, a.ifs.len() - 1));
                n0: long = a.blockLen(w0.body);
                for j0 in 0..n0 { body.push(a.stmtIdAt(w0.body, j0)); }
                a.whiles.set(st.at, WhileNode { cond: a.leaf(Op.Literal, Payload.Num(1), Lit.Bool),
                                                body: a.addBlock(body), step: w0.step });
            }
            w: WhileNode = a.whiles.get(st.at);
            self.ownScanUses(a, w.cond);
            self.ownEnterLoop();
            if (!self.ownBlock(a, w.body)) { self.ownCheckLoopMoves(); }
            if (w.step >= 0) { self.ownBlock(a, w.step); }
            self.ownLeaveLoop();
            out.push(id);
            return false;
        }
        if (st.kind == StmtKind.Loop) {
            self.ownEnterLoop();
            if (!self.ownBlock(a, a.blockStmts.get(st.at).body)) { self.ownCheckLoopMoves(); }
            self.ownLeaveLoop();
            out.push(id);
            return false;
        }
        if (st.kind == StmtKind.Unsafe || st.kind == StmtKind.Block) {
            // An ordinary nested scope, and as final as what it holds: `unsafe { return … }`
            // cannot fall through, and a block that cannot fall through publishes nothing.
            if (st.kind == StmtKind.Unsafe) { self.ownUnsafe = self.ownUnsafe + 1; }
            d: bool = self.ownBlock(a, a.blockStmts.get(st.at).body);
            if (st.kind == StmtKind.Unsafe) { self.ownUnsafe = self.ownUnsafe - 1; }
            out.push(id);
            return d;
        }
        if (st.kind == StmtKind.With) {
            self.ownBlock(a, a.withs.get(st.at).body);
            out.push(id);
            return false;
        }
        if (st.kind == StmtKind.Recover) { return self.ownRecoverStmt(a, out, st.at, id); }
        if (st.kind == StmtKind.Break || st.kind == StmtKind.Continue) {
            // A move carried here would be performed again next time round (`continue`), or
            // would leave the value moved and still named after the loop (`break`), and no
            // merge here describes either.
            self.ownCheckLoopMoves();
            self.ownLoopDrops(a, out);
            out.push(id);
            return true;
        }
        if (st.kind == StmtKind.Match) {
            self.ownMatch(a, st.at);
            out.push(id);
            return false;
        }
        if (st.kind == StmtKind.Asm) {
            nd: AsmNode = a.asms.get(st.at);
            for k in 0..nd.pieceCount {
                self.ownScanUses(a, a.asmPieces.get(nd.firstPiece + k).value);
            }
            at: long = out.len();
            out.push(id);
            mv: long = out.len();
            for k in 0..nd.pieceCount {
                self.ownApplyMoves(a, out, a.asmPieces.get(nd.firstPiece + k).value);
            }
            self.ownMovesFirst(out, at, mv);
            return nd.noReturn;
        }
        if (st.kind == StmtKind.Destructure) {
            ds: DestructureNode = a.destructures.get(st.at);
            self.ownScanUses(a, ds.value);
            at: long = out.len();
            out.push(id);
            mv: long = out.len();
            self.ownApplyMoves(a, out, ds.value);
            self.ownMovesFirst(out, at, mv);
            for k in 0..ds.nameCount {           // each target now owns its part
                t: Sym = a.names.get(ds.firstName + k);
                if (self.dropOf.has(nameOf(t))) {
                    self.ownUnmark(t);
                    self.fresh.remove(nameOf(t));
                    self.ownSetFlag(a, out, t, 0);
                }
            }
            return false;
        }
        out.push(id);
        return false;
    }

    // ─── loops ───────────────────────────────────────────────────────────────

    ownEnterLoop &self -> void {
        self.loopDepth = self.loopDepth + 1;
        self.loopBase.push(self.scope.len());
        self.loopMovedBase.push(self.loopMoved.len());
        for k in 0..self.moved.len() { self.loopMoved.push(self.moved.get(k)); }
        self.pmustLoopBase.push(self.pmustLoop.len());
        self.pmustLoop.extend(self.pmust);
    }
    ownLeaveLoop &self -> void {
        // A move that reached the back edge or a `break` has already been refused, so anything
        // still marked from a scope outside the loop was moved only on a path that returned,
        // which is not a path that gets here. Carrying it out would poison the code after the
        // loop and make a real later move skip its flag store.
        k: long = 0;
        while (k < self.moved.len()) {
            if (self.ownRepeatingMove(self.moved.get(k))) { self.moved.removeAt(k); }
            else { k = k + 1; }
        }
        // A loop may run no times, so what it did to a partial move is not certain afterwards:
        // one made before it is still there on the path that skipped it, and is certain after it
        // only if it was certain both ways. (A whole value has its own flag at every release, so
        // only these need the merge.)
        base: long = self.loopMovedBase.last();
        for k in base..self.loopMoved.len() {
            m: Sym = self.loopMoved.get(k);
            if (self.isPartial(m) && !self.ownIsMoved(m)) { self.moved.push(m); }
        }
        pb: long = self.pmustLoopBase.pop();
        before: Vec<Sym>;
        for k in pb..self.pmustLoop.len() { before.push(self.pmustLoop.get(k)); }
        while (self.pmustLoop.len() > pb) { self.pmustLoop.pop(); }
        k = 0;
        while (k < self.pmust.len()) {
            if (!symIn(before, self.pmust.get(k))) { self.pmust.removeAt(k); } else { k = k + 1; }
        }
        while (self.loopMoved.len() > base) { self.loopMoved.pop(); }
        self.loopMovedBase.pop();
        self.loopBase.pop();
        self.loopDepth = self.loopDepth - 1;
    }
    // Did this loop move a value out of a scope that outlives it? That is the repeating move,
    // and the only one the rule is about: a move the code before the loop already made goes
    // round no more times than it did.
    ownRepeatingMove &self n:Sym -> bool {
        if (self.loopMovedBase.len() == 0) { return false; }
        for k in self.loopMovedBase.last()..self.loopMoved.len() {
            if (self.loopMoved.get(k) == n) { return false; }
        }
        q: Sym = n;
        if (self.isPartial(n)) { q = self.partialOwner(n); }     // a field goes round with its owner
        if (!self.dropDepth.has(nameOf(q))) { return false; }
        return self.dropDepth.get(nameOf(q)) < self.loopDepth;
    }
    ownCheckLoopMoves &self -> void {
        for k in 0..self.moved.len() {
            n: Sym = self.moved.get(k);
            if (self.ownRepeatingMove(n)) {
                failStr(format("cannot move `{}` inside a loop\nnote: it lives outside the loop, so the move would repeat on the next turn, or leave it moved after the loop\nhelp: clone it instead", nameOf(n)));
            }
        }
    }

    // ─── branches ────────────────────────────────────────────────────────────
    //
    // The union is over the paths that reach the code after the branch, and an arm that cannot
    // fall through is not one of them: what a returning arm moved is moved on no path that gets
    // here. It still starts from the state before, which is the not-taken path of a chain with
    // no `else`, so moving in one arm and using after the `if` stays an error.

    // The first condition was read by the caller, before what it moves was recorded.
    ownIf &self inout a:Ast at:long firstScanned:bool -> void {
        before: Vec<Sym>; uni: Vec<Sym>;
        for k in 0..self.moved.len() { before.push(self.moved.get(k)); uni.push(self.moved.get(k)); }
        mustBefore: Vec<Sym>; mustAcc: Vec<Sym>;
        mustBefore.extend(self.pmust);
        reached: bool = false;
        elsed: bool = false;
        c: long = at;
        while (c >= 0) {
            nd: IfNode = a.ifs.get(c);
            // An `else if` whose condition needs statements of its own becomes an `else` holding
            // them and the rest of the chain: `else { c: bool = <cond>; if (c) { ... } else ... }`,
            // so they run only on the path that reaches that condition.
            if (c != at && self.ownCondNeeds(a, nd.cond, true)) {
                inner: Vec<long>;
                t: Sym = self.ownCondDecl(a, &inner, nd.cond);
                a.ifs.push(IfNode { cond: a.leafOf(Op.Lvalue, Payload.Name(t), Lit.Bool, NO_SYM),
                                    body: nd.body, elseIf: nd.elseIf });
                inner.push(a.addStmt(StmtKind.If, a.ifs.len() - 1));
                nd = IfNode { cond: a.leaf(Op.Literal, Payload.Num(1), Lit.Bool),
                              body: a.addBlock(inner), elseIf: -1 };
                a.ifs.set(c, nd);
            }
            // Each condition reads the values as the chain found them: an earlier link's body
            // ran on another path.
            self.ownRestore(&before);
            self.pmust.clear(); self.pmust.extend(mustBefore);
            if (c != at || !firstScanned) { self.ownScanUses(a, nd.cond); }
            if (!self.ownBlock(a, nd.body)) {
                self.ownUnion(&uni);
                self.mustMeet(&mustAcc, reached);
                reached = true;
            }
            elsed = isAlways(a, nd.cond);
            c = nd.elseIf;
        }
        self.ownRestore(&uni);
        // A chain with no `else` also falls through untaken.
        self.pmust.clear();
        if (!elsed) { self.pmust.extend(mustBefore); self.mustMeet(&mustAcc, reached); reached = true; }
        if (reached) { self.pmust.clear(); self.pmust.extend(mustAcc); } else { self.pmust.extend(mustBefore); }
    }

    // A path reaching a merge: what it moved for certain, met with what the paths before it did.
    mustMeet &self inout acc:Vec<Sym> seen:bool -> void {
        if (!seen) { acc.clear(); acc.extend(self.pmust); return; }
        k: long = 0;
        while (k < acc.len()) {
            if (!symIn(self.pmust, acc.get(k))) { acc.removeAt(k); } else { k = k + 1; }
        }
    }

    // A condition computed by statements of its own: `__condN: bool = <cond>;`, appended to
    // `out` unwalked (the walk of the block it lands in does that). The new name.
    ownCondDecl &self inout a:Ast inout out:Vec<long> cond:NodeId -> Sym {
        t: Sym = internString(format("__cond{}", self.ownSeq));
        self.ownSeq = self.ownSeq + 1;
        a.decls.push(VarDeclNode { name: t, kind: Lit.Bool, structName: NO_SYM,
                                   isArray: false, count: 0, conv: Conv.None, isVariadic: false,
                                   elemKind: Lit.Void, elemStruct: NO_SYM, init: cond });
        out.push(a.addStmt(StmtKind.VarDecl, a.decls.len() - 1));
        return t;
    }

    // Does evaluating this expression need statements of its own: an owning temporary to build
    // and release, or a tracked value to move? The same walk as `ownHoistTemps`, asking only.
    ownCondNeeds &self inout a:Ast id:NodeId borrowed:bool -> bool {
        if (id == NO_NODE) { return false; }
        e: Expr = a.expr(id);
        if (borrowed && self.ownIsOwningRvalue(e)) { return true; }
        if (e.left != NO_NODE || e.right != NO_NODE) {
            if (self.ownCondNeeds(a, e.left, false)) { return true; }
            return self.ownCondNeeds(a, e.right, false);
        }
        p: Payload = e.payload;
        match p {
            Call(c) {
                cn: CallNode = a.calls.get(c);
                at: long = self.fnNodeOf(cn.name);
                base: long = 0;
                if (cn.receiver != NO_NODE) {
                    base = 1;
                    takes: bool = self.argConsumes(a, at, cn, 0);
                    if (takes && self.ownBareDropVar(a, cn.receiver) != NO_SYM) { return true; }
                    if (self.ownCondNeeds(a, cn.receiver, !takes)) { return true; }
                }
                for k in 0..cn.argCount {
                    arg: NodeId = a.argAt(cn, k);
                    takes: bool = self.argConsumes(a, at, cn, base + k);
                    if (takes && self.ownBareDropVar(a, arg) != NO_SYM) { return true; }
                    if (self.ownCondNeeds(a, arg, !takes)) { return true; }
                }
            }
            Field(f) { return self.ownCondNeeds(a, a.fields.get(f).base, true); }
            Index(i) {
                ix: IndexNode = a.indexes.get(i);
                if (self.ownCondNeeds(a, ix.base, true)) { return true; }
                return self.ownCondNeeds(a, ix.index, false);
            }
            Lit(l) {
                ln: LitNode = a.lits.get(l);
                for k in 0..ln.initCount {
                    v: NodeId = a.inits.get(ln.firstInit + k).value;
                    if (self.ownBareDropVar(a, v) != NO_SYM) { return true; }
                    if (self.ownCondNeeds(a, v, false)) { return true; }
                }
            }
            Sub(v) { return self.ownCondNeeds(a, v, false); }
            _ { }
        }
        return false;
    }

    // `l && r` / `l || r` whose right operand needs statements: those may run only when the left
    // does not decide the answer, and after it, so the operator becomes statements ahead of the
    // one it is in. `__scN: bool = l; if (__scN) { <r's temporaries>; __scN = r; <released> }`
    // (`if (!__scN)` for `||`), and the node becomes a read of `__scN`. The left operand's
    // temporaries and moves are the enclosing statement's as before; the right's happen inside.
    ownShortCircuit &self inout a:Ast inout pre:Vec<long> inout temps:Vec<Sym> id:NodeId -> void {
        e: Expr = a.expr(id);
        self.ownHoistTemps(a, pre, temps, e.left, false);
        t: Sym = internString(format("__sc{}", self.ownSeq));
        self.ownSeq = self.ownSeq + 1;
        a.decls.push(VarDeclNode { name: t, kind: Lit.Bool, structName: NO_SYM,
                                   isArray: false, count: 0, conv: Conv.None, isVariadic: false,
                                   elemKind: Lit.Void, elemStruct: NO_SYM, init: e.left });
        lat: long = pre.len();
        pre.push(a.addStmt(StmtKind.VarDecl, a.decls.len() - 1));
        lmv: long = pre.len();
        self.ownApplyMoves(a, pre, e.left);
        self.ownMovesFirst(pre, lat, lmv);
        // The right operand is read after the left's moves, which is when it runs.
        inner: Vec<long>;
        itemps: Vec<Sym>;
        self.ownScanUses(a, e.right);
        self.ownHoistTemps(a, &inner, &itemps, e.right, false);
        asn: NodeId = a.binary(Op.Assignment, a.leafOf(Op.Lvalue, Payload.Name(t), Lit.Bool, NO_SYM),
                               e.right, Lit.Bool);
        a.exprStmts.push(ExprStmtNode { value: asn });
        rat: long = inner.len();
        inner.push(a.addStmt(StmtKind.Expr, a.exprStmts.len() - 1));
        self.pCond = self.pCond + 1;          // what the right operand moves, it moves on some paths
        rmv: long = inner.len();
        self.ownApplyMoves(a, &inner, e.right);
        self.ownMovesFirst(&inner, rat, rmv);
        self.pCond = self.pCond - 1;
        self.ownReleaseTemps(a, &inner, &itemps);
        test: NodeId = a.leafOf(Op.Lvalue, Payload.Name(t), Lit.Bool, NO_SYM);
        if (e.op == Op.LogicalOr) { test = a.unary(Op.LogicalNot, test, Lit.Bool); }
        a.ifs.push(IfNode { cond: test, body: a.addBlock(inner), elseIf: -1 });
        pre.push(a.addStmt(StmtKind.If, a.ifs.len() - 1));
        a.setExpr(id, Expr { op: Op.Lvalue, left: NO_NODE, right: NO_NODE, kind: Lit.Bool,
                             structName: NO_SYM, isParen: false, payload: Payload.Name(t) });
    }

    // Each arm answers for one variant, so an arm that binds an owning payload takes it out of
    // the value and one that does not leaves the value owning it. Nothing here records that: the
    // binding is an ordinary `v = subject.$V$k;` at the head of the arm, and the ordinary
    // payload-move rule on that store is what marks the subject and writes its flag. Recording it
    // here, ahead of the walk, would make that very store a read of a value ownership had already
    // given away, and every program matching on a Drop payload would be refused.
    ownMatch &self inout a:Ast at:long -> void {
        m: MatchNode = a.matches.get(at);
        before: Vec<Sym>; uni: Vec<Sym>;
        for k in 0..self.moved.len() { before.push(self.moved.get(k)); uni.push(self.moved.get(k)); }
        allDiverge: bool = true;
        mustBefore: Vec<Sym>; mustAcc: Vec<Sym>;
        mustBefore.extend(self.pmust);
        for k in 0..m.armCount {
            // Every arm's test reads the value as the match found it, before any arm ran.
            self.ownRestore(&before);
            self.pmust.clear(); self.pmust.extend(mustBefore);
            self.ownScanUses(a, a.arms.get(m.firstArm + k).test);
            self.bindSubject = NO_SYM;
            if (!self.ownBlock(a, a.arms.get(m.firstArm + k).body)) {
                self.mustMeet(&mustAcc, !allDiverge);
                allDiverge = false;
                self.ownUnion(&uni);
            }
        }
        self.pmust.clear();
        if (allDiverge && m.armCount > 0) { self.ownRestore(&before); self.pmust.extend(mustBefore); }
        else {
            self.ownRestore(&uni);
            if (allDiverge) { self.pmust.extend(mustBefore); } else { self.pmust.extend(mustAcc); }
        }
    }

    // `recover { body } else { handler }`. The handler can be entered from any call in the body,
    // so it starts with everything the body moved anywhere counted as possibly moved, which each
    // value's flag settles at run time. The tracked locals the body declared are out of scope
    // there, but they may hold something when a `raise` arrives: the handler first releases each
    // one its flag says still owns. Those flags are set (to "nothing to release") ahead of the
    // statement, so a `raise` before a declaration is reached finds nothing to release either.
    // Afterwards the two paths meet as an `if` and its `else` do.
    ownRecoverStmt &self inout a:Ast inout out:Vec<long> at:long id:long -> bool {
        w: WhileNode = a.whiles.get(at);
        before: Vec<Sym>; mustBefore: Vec<Sym>;
        before.extend(self.moved);
        mustBefore.extend(self.pmust);
        self.ownRecover = self.ownRecover + 1;
        self.recLocalsBase.push(self.recLocals.len());
        self.recMovedBase.push(self.recMoved.len());
        bodyExits: bool = self.ownBlock(a, w.body);
        self.ownRecover = self.ownRecover - 1;
        afterBody: Vec<Sym>; mustBody: Vec<Sym>;
        afterBody.extend(self.moved);
        mustBody.extend(self.pmust);

        entry: Vec<Sym>;
        entry.extend(before);
        for k in self.recMovedBase.last()..self.recMoved.len() {
            n: Sym = self.recMoved.get(k);
            if (!symIn(entry, n)) { entry.push(n); }
        }
        self.ownRestore(&entry);
        self.pmust.clear(); self.pmust.extend(mustBefore);
        // The releases are made against the handler's starting state (which fields of a partly
        // moved value may be gone), and set each flag, so a `raise` in the handler that reaches a
        // `recover` further out does not release them again.
        held: Vec<OwnLocal>;
        for k in self.recLocalsBase.last()..self.recLocals.len() { held.push(self.recLocals.get(k)); }
        releases: Vec<long>;
        was: long = self.ownRecover;
        self.ownRecover = 1;
        k: long = held.len();
        while (k > 0) { k = k - 1; self.ownRelease(a, &releases, held.get(k)); }
        self.ownRecover = was;
        handlerExits: bool = self.ownBlock(a, w.step);
        hb: long = w.step;
        first: long = a.stmtRuns.len();
        a.stmtRuns.extend(releases);
        for j in 0..a.blockLen(hb) { a.stmtRuns.push(a.stmtIdAt(hb, j)); }
        a.blocks.set(hb, Block { firstStmt: first, stmtCount: a.stmtRuns.len() - first });

        // What the body declares starts out owning nothing, as far as its handler can tell.
        for j in 0..held.len() { self.ownFlagDecl(a, out, held.get(j).name, 1); }
        self.recLocalsBase.pop();
        self.recMovedBase.pop();
        if (self.ownRecover == 0) { self.recLocals.clear(); self.recMoved.clear(); }
        out.push(id);

        if (bodyExits && handlerExits) {
            self.ownRestore(&before);
            self.pmust.clear(); self.pmust.extend(mustBefore);
            return true;
        }
        if (bodyExits) { return false; }
        if (handlerExits) {
            self.ownRestore(&afterBody);
            self.pmust.clear(); self.pmust.extend(mustBody);
            return false;
        }
        mustAcc: Vec<Sym>;
        mustAcc.extend(mustBody);
        self.mustMeet(&mustAcc, true);
        self.ownUnion(&afterBody);
        self.ownRestore(&afterBody);
        self.pmust.clear(); self.pmust.extend(mustAcc);
        return false;
    }

    ownRestore &self inout snap:Vec<Sym> -> void {
        self.moved.clear();
        self.moved.extend(snap);
    }
    ownUnion &self inout into:Vec<Sym> -> void {
        for k in 0..self.moved.len() {
            n: Sym = self.moved.get(k);
            seen: bool = false;
            for j in 0..into.len() { if (into.get(j) == n) { seen = true; } }
            if (!seen) { into.push(n); }
        }
    }

    // ─── returns ─────────────────────────────────────────────────────────────

    ownReturn &self inout a:Ast inout out:Vec<long> at:long id:long -> void {
        r: ReturnNode = a.returns.get(at);
        self.ownScanUses(a, r.value);
        temps: Vec<Sym>;
        self.ownHoistTemps(a, out, &temps, r.value, false);
        // Returning a borrow moves nothing, so nothing has to be describable; returning a value
        // does, and this is where a move that cannot be recorded is refused.
        if (a.fns.get(self.ownFn).returnKind != Lit.Ref) {
            self.ownRejectMove(a, r.value, "returned");
        }
        n: Sym = self.ownBareDropVar(a, r.value);
        if (n != NO_SYM) { self.ownMarkMoved(a, out, n); }
        else { self.ownApplyMoves(a, out, r.value); }
        // The drops go after the value is computed: the returned expression is evaluated by
        // this statement, so releasing the frame ahead of it hands `return v.len()` a freed
        // vector. A value that is more than a name is therefore taken into a temporary first.
        // A temporary's release has to sit after the value is computed and the return is what
        // computes it, so one is enough to force the value into a name of its own.
        if ((self.scope.len() > 0 || temps.len() > 0)
            && r.value != NO_NODE && !self.ownIsSimple(a, r.value)) {
            e: Expr = a.expr(r.value);
            t: Sym = internString(format("__ret{}", self.ownSeq));
            self.ownSeq = self.ownSeq + 1;
            a.decls.push(VarDeclNode { name: t, kind: e.kind, structName: e.structName,
                                       isArray: false, count: 0, conv: Conv.None,
                                       isVariadic: false, elemKind: Lit.Void,
                                       elemStruct: NO_SYM, init: r.value });
            out.push(a.addStmt(StmtKind.VarDecl, a.decls.len() - 1));
            a.returns.set(at, ReturnNode { value: a.leafOf(Op.Lvalue, Payload.Name(t),
                                                           e.kind, e.structName) });
        }
        self.ownReleaseTemps(a, out, &temps);
        self.ownAllScopeDrops(a, out);
        out.push(id);
    }

    // A value the scope's releases cannot disturb, and so one they may be emitted ahead of.
    ownIsSimple &self inout a:Ast id:NodeId -> bool {
        op: Op = a.expr(id).op;
        return op == Op.Literal || op == Op.Lvalue || op == Op.StringLit;
    }

    // ─── moves ───────────────────────────────────────────────────────────────

    ownMarkMoved &self inout a:Ast inout out:Vec<long> n:Sym -> void {
        if (self.ownIsMoved(n)) { return; }
        if (self.ownRecover > 0) { self.recMoved.push(n); }
        if (self.isPartial(n)) {
            self.moved.push(n);
            self.stmtMoves = self.stmtMoves + 1;
            if (self.pCond == 0) { self.pmust.push(n); }
            self.ownFlagHole(a, out, n, 1);
            return;
        }
        self.ownSetFlag(a, out, n, 1);
        self.moved.push(n);
        self.stmtMoves = self.stmtMoves + 1;
    }

    // The tracked local this expression takes the value of, or NO_SYM when it takes nobody's.
    ownBareDropVar &self inout a:Ast id:NodeId -> Sym {
        if (id == NO_NODE) { return NO_SYM; }
        e: Expr = a.expr(id);
        if (e.op != Op.Lvalue) {
            n: Sym = self.fieldMoveOf(a, id);          // `h.r` takes `r` out of `h`
            if (n != NO_SYM && self.dropOf.has(nameOf(n))) {
                match e.payload { Field(f) { return self.partialEntry(n, a.fields.get(f).name); } _ { } }
            }
            return NO_SYM;
        }
        p: Payload = e.payload;
        match p {
            Name(n) { if (self.dropOf.has(nameOf(n))) { return n; } }
            _ { }
        }
        return NO_SYM;
    }

    // `h.r` where `h` owns and `r` releases: the owner `h`, from which the field is taken (a
    // partial move, `partialEntry`). An array element has no owner to record a move on, and is
    // refused instead. A tuple's element is a field like any other.
    fieldMoveOf &self inout a:Ast id:NodeId -> Sym {
        if (id == NO_NODE) { return NO_SYM; }
        e: Expr = a.expr(id);
        if (e.op != Op.FieldAccess) { return NO_SYM; }
        if (e.kind != Lit.Struct || !gReg.needsDrop(e.structName)) { return NO_SYM; }
        p: Payload = e.payload;
        match p {
            Field(f) {
                fn: FieldNode = a.fields.get(f);
                if (isPayloadField(fn.name)) { return NO_SYM; }   // an enum payload
                return self.convBareName(a, fn.base);
            }
            _ { }
        }
        return NO_SYM;
    }

    // A move this machinery cannot describe. Every arm asks one question (after the value is
    // taken, what still believes it owns the resource?) and refuses where the answer cannot be
    // written down. A per-variable `__moved_` flag is the only place a move can be recorded, and
    // these are the shapes that have no flag to record it on. `what` says how the value is moved
    // ("returned", "handed to a parameter that takes it"), for the note: "it is <what>".
    ownRejectMove &self inout a:Ast id:NodeId what:str -> void {
        if (id == NO_NODE) { return; }
        e: Expr = a.expr(id);
        // A borrow names a value someone else owns. Copying it out (which is what moving a ref
        // expression would be) makes a second owner of one resource. That includes a borrowed
        // parameter (`&self`, `inout`): its caller kept the original and releases it, so a
        // callee handing it on to a sink would release it twice.
        if (e.kind == Lit.Ref && gReg.needsDrop(e.structName)) {
            failStr(format("cannot move a value of type `{}` out of a borrow\nnote: it is {}, and its owner would release it too\nhelp: clone it, or take it out through the owner (`pop`, `take`)",
                           nameOf(e.structName), what));
        }
        if (e.kind != Lit.Struct || !gReg.needsDrop(e.structName)) { return; }
        p: Payload = e.payload;
        match p {
            Name(n) {
                // A global is nobody's to give away: it holds its value for the whole run, so
                // what took it would release a resource the global still names, and the next
                // reader (or the next taker) uses freed memory.
                if (e.op == Op.Lvalue && gReg.findGlobalSym(n) >= 0) {
                    failStr(format("cannot move out of the global `{}`\nnote: it is {}, and the global keeps naming the value, which would be released twice\nhelp: borrow it with `&`, clone it, or take it out with `take(&{})`",
                                   nameOf(n), what, nameOf(n)));
                }
            }
            Index(i) {
                // An element has no flag of its own, so a move out of one cannot be recorded,
                // and behind a raw pointer the compiler never owned it to begin with.
                if (a.indexes.get(i).rawPointerBase) { return; }
                failStr(format("cannot move a value of type `{}` out of an element\nnote: it is {}, and what holds the element (the array, or the owner of the slice or vector) still releases it, so it would be released twice\nhelp: borrow it with `&`, clone it (`.clone()`), or take it out through its owner (`pop`, `removeAt`, `take`, `replace`, `swapValues`)",
                               nameOf(e.structName), what));
            }
            Field(f) {
                fn: FieldNode = a.fields.get(f);
                if (isPayloadField(fn.name)) { return; }   // an enum payload: tracked
                fld: str = fieldSpelling(fn.name);
                owner: Sym = self.ownPlaceRoot(a, fn.base);
                if (owner == NO_SYM || !self.dropOf.has(nameOf(owner))) {
                    failStr(format("cannot move the field `{}` out of a value this function does not own\nnote: it is {}, and its real owner would release it too\nhelp: borrow it with `&`, clone it (`.clone()`), or take it out through its owner (`take`, `replace`, `swapValues` on a place it lends you `inout`)",
                                   fld, what));
                }
                if (a.expr(fn.base).op != Op.Lvalue) {                 // `h.a.b`: only `h`'s fields are tracked
                    failStr(format("cannot move the field `{}` out of a nested field of `{}`\nnote: it is {}, and a move is tracked per field of a local, so only a direct field can be taken\nhelp: clone it (`.clone()`), take the outer field first, or take it out with `take`, `replace` or `swapValues`",
                                   fld, nameOf(owner), what));
                }
                sn: Sym = intern(nameOf(self.dropOf.get(nameOf(owner))));
                // A hand-written `drop` must still run, and it reads every field: taking one out
                // would hand it a value with a hole in it. The glue keeps the author's release
                // under `$own`, which is what says there was one. (Rust's rule, E0509.)
                if (self.fnNodeOf(internString(format("{}_drop$own", nameOf(sn)))) >= 0) {
                    failStr(format("cannot move the field `{}` out of `{}`\nnote: it is {}, and `{}` implements `Drop`, whose `drop` must still run on the whole value, so it cannot be partly moved\nhelp: clone the field, or give `{}` a method that takes the value apart",
                                   fld, nameOf(owner), what, nameOf(sn), nameOf(sn)));
                }
            }
            _ { }
        }
    }

    // An argument a parameter takes is moved like a stored or returned value, so every move a
    // store refuses is refused here too: a borrow, a whole global, an element (of an array, a
    // slice, a borrowed value), and a field of a value this function does not own or of a field.
    // Each is a second owner of one resource: the callee releases it, and so does whoever still
    // holds the place (`dst.push(xs[i])` with `xs: [String]` would leave two vectors sharing a
    // buffer).
    ownRejectMoveArg &self inout a:Ast id:NodeId callee:Sym -> void {
        if (id == NO_NODE) { return; }
        e: Expr = a.expr(id);
        if (!gReg.needsDrop(e.structName)) { return; }
        if (e.kind == Lit.Ref) { self.ownRejectMove(a, id, "handed to a parameter that takes it"); return; }
        if (e.kind != Lit.Struct) { return; }
        match e.payload {
            Name(n) { self.ownRejectMove(a, id, "handed to a parameter that takes it"); }
            Index(i) { self.ownRejectMove(a, id, "handed to a parameter that takes it"); }
            Field(f) { self.ownRejectMove(a, id, "handed to a parameter that takes it"); }
            _ { }
        }
    }

    dropFieldCount &self sn:Sym -> long {
        at: long = gReg.findStructSym(sn);
        if (at < 0) { return 0; }
        d: StructDef = gReg.structDef(at);
        n: long = 0;
        for k in 0..d.fieldCount {
            f: FieldDef = gReg.fieldAt(d, k);
            if (f.kind == Lit.Struct && gReg.needsDrop(f.structName)) { n = n + 1; }
        }
        return n;
    }

    // Every move an expression performs: a tracked value handed to a parameter that takes it,
    // or stored into an aggregate, which owns it from then on, exactly as a sink does.
    ownApplyMoves &self inout a:Ast inout out:Vec<long> id:NodeId -> void {
        if (id == NO_NODE) { return; }
        e: Expr = a.expr(id);
        self.ownApplyMoves(a, out, e.left);
        self.ownApplyMoves(a, out, e.right);
        p: Payload = e.payload;
        match p {
            Sub(v)  { self.ownApplyMoves(a, out, v); }
            Call(c) { self.ownCallMoves(a, out, c); }
            Lit(l)  {
                ln: LitNode = a.lits.get(l);
                for k in 0..ln.initCount {
                    v: NodeId = a.inits.get(ln.firstInit + k).value;
                    if (self.stmtMoves > 0) { self.ownScanUses(a, v); }    // in order, as a call's
                    if (a.expr(v).op == Op.Lvalue && a.expr(v).kind == Lit.Struct) {
                        match a.expr(v).payload { Name(g) { self.ownRejectMove(a, v, "stored in a literal"); } _ { } }
                    }
                    // A whole array of a Drop type moved into the literal's field.
                    if (a.expr(v).kind == Lit.Struct && gReg.needsDrop(a.expr(v).structName)
                        && a.expr(v).op != Op.ArrayLit && self.ownWholeArray(a, v) > 0) {
                        self.ownMarkMoved(a, out, self.ownArraySource(a, v));
                        continue;
                    }
                    n: Sym = self.ownBareDropVar(a, v);
                    if (n != NO_SYM) { self.ownMarkMoved(a, out, n); }
                    else { self.ownApplyMoves(a, out, v); }
                }
            }
            Index(i) {
                ix: IndexNode = a.indexes.get(i);
                self.ownApplyMoves(a, out, ix.base);
                self.ownApplyMoves(a, out, ix.index);
            }
            Field(f) { self.ownApplyMoves(a, out, a.fields.get(f).base); }
            _ { }
        }
    }

    ownCallMoves &self inout a:Ast inout out:Vec<long> c:long -> void {
        cn: CallNode = a.calls.get(c);
        at: long = self.fnNodeOf(cn.name);
        base: long = 0;
        // The receiver is parameter 0 and is consumed like any other: `self` by value is how a
        // method that takes the value out (`unwrap`, `pop`) says so, and the option it came
        // from must not be released again at scope exit.
        //
        // In evaluation order, left to right: an operand evaluated after a move made earlier in
        // the same statement reads what was moved (`f(take(r), look(r))`), which the scan made
        // before the statement could not see. So once this statement has moved something, each
        // later operand is scanned again against the moves so far.
        if (cn.receiver != NO_NODE) {
            base = 1;
            rn: Sym = NO_SYM;
            if (self.stmtMoves > 0) { self.ownScanUses(a, cn.receiver); }
            if (self.argConsumes(a, at, cn, 0)) {
                self.ownRejectMoveArg(a, cn.receiver, cn.name);
                rn = self.ownBareDropVar(a, cn.receiver);
            }
            if (rn != NO_SYM) { self.ownMarkMoved(a, out, rn); }
            else { self.ownApplyMoves(a, out, cn.receiver); }
        }
        for k in 0..cn.argCount {
            arg: NodeId = a.argAt(cn, k);
            n: Sym = NO_SYM;
            if (self.stmtMoves > 0) { self.ownScanUses(a, arg); }
            if (self.argConsumes(a, at, cn, base + k)) {
                self.ownRejectMoveArg(a, arg, cn.name);
                n = self.ownBareDropVar(a, arg);
            }
            if (n != NO_SYM) { self.ownMarkMoved(a, out, n); }
            else { self.ownApplyMoves(a, out, arg); }
        }
    }

    // Error on reading a value this path has already handed on. A read also settles that the
    // local is no longer fresh: something looked at what it holds.
    ownScanUses &self inout a:Ast id:NodeId -> void {
        if (id == NO_NODE) { return; }
        e: Expr = a.expr(id);
        self.ownScanUses(a, e.left);
        self.ownScanUses(a, e.right);
        p: Payload = e.payload;
        match p {
            Name(n) {
                if (self.ownIsMoved(n)) { self.ownMovedUse(a, n); }
                if (self.hasPartial(n)) { self.ownPartialUse(a, n); }
                self.fresh.remove(nameOf(n));
            }
            Sub(v)  {
                self.ownScanUses(a, v);
                if (e.op == Op.AddressOf && self.ownUnsafe > 0) {
                    ve: Expr = a.expr(v);
                    if (ve.op == Op.Lvalue) {
                        match ve.payload {
                            Name(x) {
                                if (self.dropOf.has(nameOf(x)) && !symIn(self.addrFills, x)) { self.addrFills.push(x); }
                            }
                            _ { }
                        }
                    }
                }
            }
            Field(f) {
                // `x.g` reads one field: what was taken out of `x` matters only if it is `g`.
                fnode: FieldNode = a.fields.get(f);
                be: Expr = a.expr(fnode.base);
                x: Sym = NO_SYM;
                if (be.op == Op.Lvalue) { match be.payload { Name(bn) { x = bn; } _ { } } }
                if (x != NO_SYM && self.dropOf.has(nameOf(x))) {
                    if (self.ownIsMoved(x)) { self.ownMovedUse(a, x); }
                    e2: Sym = self.partialEntry(x, fnode.name);
                    if (self.ownIsMoved(e2)) {
                        failStr(format("use of moved value: `{}.{}`", nameOf(x), fieldSpelling(fnode.name)));
                    }
                    self.fresh.remove(nameOf(x));
                } else { self.ownScanUses(a, fnode.base); }
            }
            Index(i) {
                ix: IndexNode = a.indexes.get(i);
                if (ix.base == NO_NODE && self.ownIsMoved(ix.name)) { self.ownMovedUse(a, ix.name); }
                self.ownScanUses(a, ix.base);
                self.ownScanUses(a, ix.index);
                self.ownScanUses(a, ix.sliceStart);
                self.ownScanUses(a, ix.sliceEnd);
            }
            Call(c) {
                cn: CallNode = a.calls.get(c);
                self.exclusivity(a, c);
                if (cn.argCount >= 2 || (cn.argCount == 1 && cn.receiver != NO_NODE)) { self.moveWhileLent(a, cn); }
                self.ownScanUses(a, cn.receiver);
                self.ownScanUses(a, cn.callee);
                for k in 0..cn.argCount { self.ownScanUses(a, a.argAt(cn, k)); }
            }
            Lit(l) {
                ln: LitNode = a.lits.get(l);
                self.ownScanUses(a, ln.rest);
                for k in 0..ln.initCount {
                    self.ownScanUses(a, a.inits.get(ln.firstInit + k).value);
                }
            }
            _ { }
        }
    }

    // ─── temporaries ─────────────────────────────────────────────────────────
    //
    // An owning value with no name (a call's result, a struct literal) in a position that only
    // borrows it (an argument to a read parameter or a variadic, a receiver, the base of a field
    // read, an `if`'s condition, a statement of its own) belongs to nobody, and was released by
    // nobody. It is hoisted into a compiler local ahead of the statement and released right after
    // it. One in a consuming position (a sink argument, a store, a returned value, a literal's
    // field) is its destination's already and is left alone.
    //
    // The node is replaced where it stands: the original expression moves to a fresh node that
    // the temporary's declaration initializes, and the node every parent already points at
    // becomes the read of that temporary. An arena addressed by index makes that the whole of
    // the rewiring; a tree of pointers would have to hand each parent its new child.
    ownIsOwningRvalue &self e:Expr -> bool {
        if (e.kind != Lit.Struct || !gReg.needsDrop(e.structName)) { return false; }
        return e.op == Op.FunctionCall || e.op == Op.MethodCall || e.op == Op.StructLit;
    }

    ownHoist &self inout a:Ast inout pre:Vec<long> inout temps:Vec<Sym> id:NodeId -> void {
        e: Expr = a.expr(id);
        t: Sym = internString(format("__tmp{}", self.ownSeq));
        self.ownSeq = self.ownSeq + 1;
        orig: NodeId = a.addExpr(e);
        a.decls.push(VarDeclNode { name: t, kind: Lit.Struct, structName: e.structName,
                                   isArray: false, count: 0, conv: Conv.None, isVariadic: false,
                                   elemKind: Lit.Void, elemStruct: NO_SYM, init: orig });
        self.tmpDecl.put(nameOf(t), a.decls.len() - 1);
        pre.push(a.addStmt(StmtKind.VarDecl, a.decls.len() - 1));
        // What the hoisted expression itself consumed still has to be recorded: after this it
        // is reachable only through the declaration, which no later walk looks inside.
        self.ownApplyMoves(a, pre, orig);
        a.setExpr(id, Expr { op: Op.Lvalue, left: NO_NODE, right: NO_NODE, kind: Lit.Struct,
                             structName: e.structName, isParen: false, payload: Payload.Name(t) });
        temps.push(t);
    }

    ownHoistTemps &self inout a:Ast inout pre:Vec<long> inout temps:Vec<Sym> id:NodeId borrowed:bool -> void {
        if (id == NO_NODE) { return; }
        e: Expr = a.expr(id);
        if ((e.op == Op.LogicalAnd || e.op == Op.LogicalOr) && self.ownCondNeeds(a, e.right, false)) {
            self.ownShortCircuit(a, pre, temps, id);
            return;
        }
        if (e.left != NO_NODE || e.right != NO_NODE) {
            // An operator: each operand is consumed by it, or is a scalar with nothing to own.
            self.ownHoistTemps(a, pre, temps, e.left, false);
            self.ownHoistTemps(a, pre, temps, e.right, false);
        } else {
            p: Payload = e.payload;
            match p {
                Call(c) {
                    cn: CallNode = a.calls.get(c);
                    at: long = self.fnNodeOf(cn.name);
                    base: long = 0;
                    if (cn.receiver != NO_NODE) {
                        base = 1;
                        // A method whose `self` is by value consumes its receiver: `s + "x"` is
                        // `String.add`, which takes the string and hands back the grown one. A
                        // temporary in that position is the callee's, so releasing it here would
                        // free the buffer the answer is still using: `d + "a" + "b"` would print
                        // the allocator's own free-list pointer out of the middle of the string.
                        self.ownHoistTemps(a, pre, temps, cn.receiver,
                                           !self.argConsumes(a, at, cn, 0));
                    }
                    for k in 0..cn.argCount {
                        takes: bool = self.argConsumes(a, at, cn, base + k);
                        self.ownHoistTemps(a, pre, temps, a.argAt(cn, k), !takes);
                    }
                }
                Field(f) { self.ownHoistTemps(a, pre, temps, a.fields.get(f).base, true); }
                Index(i) {
                    ix: IndexNode = a.indexes.get(i);
                    self.ownHoistTemps(a, pre, temps, ix.base, true);
                    self.ownHoistTemps(a, pre, temps, ix.index, false);
                }
                Lit(l) {
                    ln: LitNode = a.lits.get(l);
                    for k in 0..ln.initCount {
                        self.ownHoistTemps(a, pre, temps, a.inits.get(ln.firstInit + k).value, false);
                    }
                }
                Sub(v) { self.ownHoistTemps(a, pre, temps, v, false); }
                _ { }
            }
        }
        if (borrowed && self.ownIsOwningRvalue(a.expr(id))) { self.ownHoist(a, pre, temps, id); }
    }

    // In reverse order of creation: a temporary built from another is released first.
    ownReleaseTemps &self inout a:Ast inout out:Vec<long> inout temps:Vec<Sym> -> void {
        k: long = temps.len();
        while (k > 0) {
            k = k - 1;
            n: Sym = temps.get(k);
            out.push(self.ownDropStmt(a, n, a.decls.get(self.tmpDecl.get(nameOf(n))).structName));
        }
        temps.clear();
    }

    // ─── the law of exclusivity, per call ────────────────────────────────────
    //
    // A borrow never outlives the call that makes it, so aliasing can only bite while one call
    // runs: an `inout` access may not overlap any other aggregate access in the same argument
    // list. An access path is the root variable plus its field and index chain; two components
    // are disjoint only when they are distinct field names, distinct roots, or two distinct
    // constant indices: an index the compiler cannot read selects any element and overlaps
    // every other.
    //
    // Checked from `ownScanUses`, which already meets every expression that can hold a call,
    // exactly once, with the conventions already decided and the body not yet rewritten.
    exclusivity &self inout a:Ast c:long -> void {
        cn: CallNode = a.calls.get(c);
        at: long = self.fnNodeOf(cn.name);
        if (at < 0) { return; }
        self.xPath.clear();
        acc: Vec<Access>;
        base: long = 0;
        if (cn.receiver != NO_NODE) {
            base = 1;
            self.noteAccess(a, &acc, at, 0, cn.receiver);
        }
        for k in 0..cn.argCount {
            self.noteAccess(a, &acc, at, base + k, a.argAt(cn, k));
        }
        for k in 0..acc.len() {
            for j in k + 1..acc.len() {
                x: Access = acc.get(k);
                y: Access = acc.get(j);
                if ((x.writes || y.writes) && self.pathsOverlap(x, y)) {
                    w: Access = x;
                    o: Access = y;
                    if (!x.writes) { w = y; o = x; }
                    failStr(format("cannot lend `{}` mutably while `{}` is also used in the call to `{}`\nhelp: clone one of them, or restructure the call",
                                   self.pathText(w), self.pathText(o), nameOf(cn.name)));
                }
            }
        }
    }

    // ─── a value moved into a call that also lends it ────────────────────────
    //
    // A parameter that takes its argument (a `sink`) owns it from the moment the call begins, and
    // may release it before the call returns. So a value that owns something may not be moved into
    // one parameter while it, or a place overlapping it, is lent to another, or to the receiver:
    // the borrow would read what the callee released (`take(x, x)` with `take r:String sink
    // s:String`, or `put(v, v.name)`). Only the lend made before the move is this check's: the move
    // made first is the ownership walk's, which refuses what comes after it as a use of a moved
    // value. Every kind of call: a direct one lends what its parameter does not take, a call
    // through a fn value what its type does not mark `sink`, and a dispatch what its trait's
    // method does not (`argConsumes`). An argument the call is not handed (`x.len()`) lends nothing
    // across it; one that is a borrow a call returned (`v.at(0)`) lends what that call borrowed.
    moveWhileLent &self inout a:Ast cn:CallNode -> void {
        base: long = 0;
        if (cn.receiver != NO_NODE) { base = 1; }
        // Most calls move nothing that owns anything, and are done with here. A move to look at is
        // an argument after the first that owns something; whether it is a move is asked below.
        owning: bool = false;
        for k in 0..cn.argCount {
            if (base + k == 0) { continue; }
            arg: NodeId = a.argAt(cn, k);
            if (a.exprs[arg].kind == Lit.Struct && gReg.needsDrop(a.exprs[arg].structName)) { owning = true; break; }
        }
        if (!owning) { return; }
        at: long = self.fnNodeOf(cn.name);
        self.xPath.clear();
        lent: Vec<Access>;
        for i in 0..base + cn.argCount {
            arg: NodeId = cn.receiver;
            if (i >= base) { arg = a.argAt(cn, i - base); }
            e: Expr = a.expr(arg);
            if (self.argConsumes(a, at, cn, i)) {
                if (lent.len() == 0 || e.kind != Lit.Struct || !gReg.needsDrop(e.structName)) { continue; }
                first: long = self.xPath.len();
                n: long = self.pathOf(a, arg);
                if (n == 0) { continue; }
                moved: Access = Access { first: first, count: n, writes: true };
                for l in lent {
                    if (self.pathsOverlap(l, moved)) {
                        failStr(format("cannot move `{}` while `{}` is also lent in the call to `{}`\nnote: the parameter that takes `{}` may release it before the call returns, while the borrow is still in use\nhelp: clone one of them, or restructure the call",
                                       self.pathText(moved), self.pathText(l), nameOf(cn.name), self.pathText(moved)));
                    }
                }
                continue;
            }
            if (byAddressKind(e.kind) && !namedScalar(e.kind, e.structName)) { self.lentPlaces(a, arg, &lent); }
        }
    }

    // The places an argument handed by address lends for the call, appended to `out` (their paths
    // to `xPath`): the place it names; for a borrow a call returned, what that call was lent; for a
    // closure, each capture.
    lentPlaces &self inout a:Ast id:NodeId inout out:Vec<Access> -> void {
        if (id == NO_NODE) { return; }
        first: long = self.xPath.len();
        n: long = self.pathOf(a, id);
        if (n > 0) { out.push(Access { first: first, count: n, writes: false }); return; }
        // Down to what the argument is made of: through `&`, a coercion to a trait object, a lent
        // place's `*r`, a field, an element.
        cur: NodeId = id;
        while (cur != NO_NODE) {
            e: Expr = a.expr(cur);
            next: NodeId = NO_NODE;
            match e.payload {
                Sub(v)   { if (e.op == Op.AddressOf || e.op == Op.MakeTraitObj || lentPlaceOf(a, cur) != NO_NODE) { next = v; } }
                Field(f) { next = a.fields.get(f).base; }
                Index(i) { next = a.indexes.get(i).base; }
                Call(c) {
                    if (e.kind != Lit.Ref && e.kind != Lit.Slice) { return; }
                    cn: CallNode = a.calls.get(c);
                    self.lentPlaces(a, cn.receiver, out);
                    for k in 0..cn.argCount { self.lentPlaces(a, a.argAt(cn, k), out); }
                    return;
                }
                Lit(l) {
                    ln: LitNode = a.lits.get(l);
                    if (!isClosureStruct(ln.typeName)) { return; }
                    for k in 0..ln.initCount { self.lentPlaces(a, a.inits.get(ln.firstInit + k).value, out); }
                    return;
                }
                _ { }
            }
            cur = next;
        }
    }

    noteAccess &self inout a:Ast inout acc:Vec<Access> at:long i:long id:NodeId -> void {
        f: FnNode = a.fns.get(at);
        if (i >= f.argCount) { return; }
        p: VarDeclNode = a.paramAt(f, i);
        if (!(p.kind == Lit.Ref || p.kind == Lit.Struct || p.kind == Lit.TraitObj
              || p.kind == Lit.Slice)) { return; }
        // ...and a backed enum is not one of those, however the parser typed it: its values are
        // its backing integer, copied into the call like any scalar, aliasing nothing. Without
        // this, `self.lowerAggValue(a, id, self.retKind, …)` reads as `self` lent mutably while
        // `self.retKind` is also accessed, which is one value being copied, not two views of it.
        if (p.kind == Lit.Struct && p.structName != NO_SYM) {
            named: str = nameOf(p.structName);
            if (gReg.isEnumType(named) && !gReg.isSumType(named)) { return; }
        }
        // A closure reaches its captures for the whole call, so each is an access of its own:
        // mutable exactly where the body writes it.
        e: Expr = a.expr(id);
        q: Payload = e.payload;
        match q {
            Lit(l) {
                ln: LitNode = a.lits.get(l);
                if (isClosureStruct(ln.typeName)) {
                    for k in 0..ln.initCount {
                        iv: InitNode = a.inits.get(ln.firstInit + k);
                        first: long = self.xPath.len();
                        n: long = self.pathOf(a, iv.value);
                        if (n > 0) {
                            acc.push(Access { first: first, count: n,
                                              writes: self.capturesMutably(a, ln.typeName, iv.name) });
                        }
                    }
                    return;
                }
            }
            _ { }
        }
        first: long = self.xPath.len();
        n: long = self.pathOf(a, id);
        if (n == 0) { return; }          // an rvalue: a fresh temporary, aliasing nothing
        // An `inout` lend mutates; a trait object may reach a `&self` method through its
        // vtable, so lending one is conservatively a mutation too.
        acc.push(Access { first: first, count: n,
                          writes: p.conv == Conv.Inout || p.kind == Lit.TraitObj });
    }

    // The place an argument names, appended to `xPath`. The answer is how many components were
    // appended: 0 for an rvalue, which lives in a temporary of its own and aliases nothing.
    pathOf &self inout a:Ast id:NodeId -> long {
        rev: Vec<Sym>;
        cur: NodeId = id;
        while (cur != NO_NODE) {
            e: Expr = a.expr(cur);
            p: Payload = e.payload;
            // A `&` and a coercion to a trait object are both views of what is under them, not
            // values of their own. Left to the `_` arm below, a `MakeTraitObj` would answer 0 ("an
            // rvalue, aliasing nothing"), so `both(s, s)` would record no access at all and the
            // mutable-lend rule in `noteAccess` would never be asked about it.
            if (e.op == Op.AddressOf || e.op == Op.MakeTraitObj || lentPlaceOf(a, cur) != NO_NODE) {
                inner: NodeId = NO_NODE;
                match p { Sub(v) { inner = v; } _ { } }
                if (inner == NO_NODE) { return 0; }
                cur = inner;
                continue;
            }
            done: bool = false;
            match p {
                Name(x) {
                    if (e.op != Op.Lvalue) { return 0; }
                    rev.push(x);
                    done = true;
                }
                Field(f) {
                    fn: FieldNode = a.fields.get(f);
                    rev.push(fn.name);
                    cur = fn.base;
                }
                Index(i) {
                    ix: IndexNode = a.indexes.get(i);
                    rev.push(self.indexComponent(a, ix.index));
                    if (ix.base == NO_NODE) { rev.push(ix.name); done = true; }
                    else { cur = ix.base; }
                }
                _ { return 0; }
            }
            if (done) {
                k: long = rev.len();
                while (k > 0) { k = k - 1; self.xPath.push(rev.get(k)); }
                return rev.len();
            }
        }
        return 0;
    }

    // `[7]` for a constant index, `[*]` for one only the running program knows, which is what
    // makes `a[i]` overlap every element while `a[0]` and `a[1]` stay disjoint.
    indexComponent &self inout a:Ast id:NodeId -> Sym {
        if (id != NO_NODE) {
            e: Expr = a.expr(id);
            if (e.op == Op.Literal) {
                p: Payload = e.payload;
                match p { Num(v) { return internString(format("[{}]", v)); } _ { } }
            }
        }
        return intern("[*]");
    }

    // Two paths overlap unless some component pair is provably disjoint. One path being a
    // prefix of the other means the shorter reaches everything the longer does.
    pathsOverlap &self x:Access y:Access -> bool {
        n: long = x.count;
        if (y.count < n) { n = y.count; }
        for k in 0..n {
            if (!self.compsOverlap(self.xPath.get(x.first + k), self.xPath.get(y.first + k))) {
                return false;
            }
        }
        return true;
    }

    compsOverlap &self p:Sym q:Sym -> bool {
        if (p == q) { return true; }
        pi: bool = strStartsWith(nameOf(p), "[");
        qi: bool = strStartsWith(nameOf(q), "[");
        // Distinct field names and distinct roots select different places; two indices are
        // disjoint only when both are constants, which `[*]` is not.
        if (pi && qi) { return nameOf(p) == "[*]" || nameOf(q) == "[*]"; }
        return false;
    }

    pathText &self x:Access -> str {
        s: String;
        for k in 0..x.count {
            c: str = nameOf(self.xPath.get(x.first + k));
            if (k > 0 && !strStartsWith(c, "[")) { s.push('.'); }
            s.pushStr(c);
        }
        return keepString(s);
    }

    // A read of a value, or of a field taken out of one, that this path has already handed on.
    ownMovedUse &self inout a:Ast n:Sym -> void {
        if (self.isPartial(n)) {
            failStr(format("use of moved value: `{}.{}`", nameOf(self.partialOwner(n)),
                           fieldSpelling(self.pField.get(nameOf(n)))));
        }
        failStr(format("use of moved value: `{}`", nameOf(n)));
    }
    // `x` as a whole after a field was taken out of it: moving it, lending it, calling a method.
    ownPartialUse &self inout a:Ast n:Sym -> void {
        for k in 0..self.moved.len() {
            m: Sym = self.moved.get(k);
            if (self.isPartial(m) && self.partialOwner(m) == n) {
                failStr(format("use of partly moved value: `{}`\nnote: field `{}` was moved out\nhelp: read the other fields one by one, or give `{}` a whole value again first",
                               nameOf(n), fieldSpelling(self.pField.get(nameOf(m))), nameOf(n)));
            }
        }
    }

    // ─── a store releases what it overwrites ─────────────────────────────────
    //
    // `x = v` where `x` already owns something: that something has to be released, or it leaks,
    // and after `v` is built, because `v` may read it (`x = x.clone()`). So the old value is
    // saved to a temporary before the store and released after it. The temporary is a bitwise
    // copy of a handle; the store itself still writes in place.

    ownExprStmt &self inout a:Ast inout out:Vec<long> id:NodeId stmt:long -> void {
        e: Expr = a.expr(id);
        temps: Vec<Sym>;
        if (e.op != Op.Assignment || e.left == NO_NODE) {
            // A statement of its own: what it computes is discarded, so an owning result is a
            // temporary to release too.
            self.ownScanUses(a, id);
            self.ownHoistTemps(a, out, &temps, id, true);
            at: long = out.len();
            out.push(stmt);
            mv: long = out.len();
            self.ownApplyMoves(a, out, id);
            self.ownMovesFirst(out, at, mv);
            self.ownReleaseTemps(a, out, &temps);
            return;
        }
        // A whole array of a Drop type: a move (`ownArrayStore`).
        le: Expr = a.expr(e.left);
        if (le.kind == Lit.Struct && gReg.needsDrop(le.structName) && a.expr(e.right).op != Op.ArrayLit
            && (self.ownWholeArray(a, e.left) > 0 || self.ownWholeArray(a, e.right) > 0)) {
            self.ownArrayStore(a, out, e, stmt);
            return;
        }
        // A later binding of the same arm reads the subject its first one already moved from:
        // the arm takes the variant's payloads together, and only the first is a use of a value
        // that might have gone.
        if (self.bindSubject == NO_SYM || self.payloadSubject(a, e.right) != self.bindSubject) {
            self.ownScanUses(a, e.right);
        }
        self.ownHoistTemps(a, out, &temps, e.right, false);
        self.ownHoistTemps(a, out, &temps, e.left, false);
        e = a.expr(id);
        // The store defines its target, so reading the target as a use would refuse the one
        // statement that brings a moved value back.
        target: Sym = self.ownBareDropVar(a, e.left);
        // `x.f = v` into a value that holds nothing yet, or was moved away whole: the store builds
        // the value up again, and it is the owner that comes back. That is sound only when `f` is
        // all it owns: any other owning field would come back holding what was moved away (or
        // nothing at all) and be released at the scope's end.
        if (target != NO_SYM && self.isPartial(target)) {
            ow: Sym = self.partialOwner(target);
            if (self.fresh.has(nameOf(ow)) || self.ownIsMoved(ow)) {
                osn: Sym = intern(nameOf(self.dropOf.get(nameOf(ow))));
                if (self.dropFieldCount(osn) > 1) {
                    why: str = "was moved away";
                    if (self.fresh.has(nameOf(ow))) { why = "holds no value yet"; }
                    failStr(format("cannot assign to the field `{}` of `{}`\nnote: `{}` {}, and it owns other fields this store would not give back\nhelp: assign `{}` a whole value",
                                   fieldSpelling(self.pField.get(nameOf(target))), nameOf(ow), nameOf(ow), why, nameOf(ow)));
                }
                target = ow;
            }
        }
        if (target == NO_SYM && a.expr(e.left).op != Op.Lvalue) { self.ownScanUses(a, e.left); }
        if (lentPlaceOf(a, e.left) != NO_NODE) { self.ownRejectMove(a, e.right, "stored through a lent parameter"); }
        else if (a.expr(e.left).kind != Lit.Ref) { self.ownRejectMove(a, e.right, "assigned to a local"); }

        moves: Vec<long>;
        n: Sym = self.ownBareDropVar(a, e.right);
        if (n == NO_SYM) {
            n = self.ownPayloadMove(a, e.right);
            if (n != NO_SYM) { self.bindSubject = n; }
        }
        if (n != NO_SYM) { self.ownMarkMoved(a, &moves, n); }
        else { self.ownApplyMoves(a, &moves, e.right); }

        sd: StoreDrop = self.ownStoreDrop(a, e.left);
        needed: bool = sd.needed;
        if (needed && sd.guard != NO_SYM && self.ownIsMoved(sd.guard)) { needed = false; }
        // ...and a first store into a declared local has nothing to release, unless it sits in
        // a loop the declaration does not: the second time round the local is not fresh at all.
        if (needed && target != NO_SYM && self.fresh.has(nameOf(target))
            && self.dropDepth.get(nameOf(target)) == self.loopDepth) { needed = false; }
        if (target != NO_SYM) { self.fresh.remove(nameOf(target)); }

        // A field taken out on every path here holds nothing to release; on some paths, its
        // flag says.
        partTarget: bool = target != NO_SYM && self.isPartial(target);
        partMoved: bool = partTarget && self.ownIsMoved(target);
        if (needed && partMoved && self.inMust(target)) { needed = false; }
        old: Sym = NO_SYM;
        if (needed) { old = self.ownSaveOld(a, out, e.left, sd.structName); }
        if (needed && old == NO_SYM) { needed = false; }
        // Inside a `recover` body the moves go first, as `ownMovesFirst` says why.
        if (self.ownRecover > 0) { out.extend(moves); moves.clear(); }
        out.push(stmt);
        if (needed) {
            if (sd.guard == NO_SYM) { out.push(self.ownDropStmt(a, old, sd.structName)); }
            else if (partMoved) {
                if (!symIn(self.pFlags, target)) { self.pFlags.push(target); }
                out.push(self.ownFlagGuard(a, sd.guard, self.ownFlagGuard(a, target, self.ownDropStmt(a, old, sd.structName))));
            }
            else if (!partTarget && target != NO_SYM && self.hasPartial(target)) {
                // The whole value replaced while a field of it was out: what is left of the old
                // one is released field by field.
                out.push(self.ownPartialDrop(a, target, old, sd.structName));
            }
            else { out.push(self.ownGuardedDrop(a, sd.guard, old, sd.structName)); }
        }
        out.extend(moves);
        // The store defines the target, so a variable the right-hand side just moved out of is
        // live again. It holds the result. `s = f(s)` is the ordinary way to write a consuming
        // update, and reviving means clearing the runtime flag too, not only the checker's.
        if (partTarget) {
            if (partMoved) {
                self.ownUnmark(target);
                self.dropMust(target);
                self.ownFlagHole(a, out, target, 0);
            }
        } else if (target != NO_SYM) {
            if (self.hasPartial(target)) {
                self.ownPartialReset(a, out, target);
                self.ownPartialForget(target);
            }
            self.ownUnmark(target);
            self.ownSetFlag(a, out, target, 0);
        }
        self.ownReleaseTemps(a, out, &temps);
    }

    // `subject.$V$k` on the right of a store: a match arm's binding prologue, which takes the
    // payload out of the value it was carried in. The move is recorded on the subject: a member
    // of a union has no flag of its own, and its owner's is what stops the scope exit releasing
    // what the arm has taken. An arm that binds nothing writes no such store and leaves the
    // value owning its payload, which is what makes the release per-path rather than static.
    payloadOf &self inout a:Ast id:NodeId -> Sym {
        if (id == NO_NODE) { return NO_SYM; }
        e: Expr = a.expr(id);
        if (e.op != Op.FieldAccess) { return NO_SYM; }
        if (e.kind != Lit.Struct || !gReg.needsDrop(e.structName)) { return NO_SYM; }
        p: Payload = e.payload;
        match p {
            Field(f) {
                fn: FieldNode = a.fields.get(f);
                nm: str = nameOf(fn.name);
                if (!isPayloadField(fn.name) || nm == enumTagField()) { return NO_SYM; }
                return self.convBareName(a, fn.base);
            }
            _ { }
        }
        return NO_SYM;
    }

    // The same, narrowed to a value this function is tracking. Convention inference asks the
    // question above before any of that exists, so the two cannot share one answer: `dropOf` is
    // the ownership walk's table and is empty while conventions are being decided.
    ownPayloadMove &self inout a:Ast id:NodeId -> Sym {
        n: Sym = self.payloadOf(a, id);
        if (n != NO_SYM && self.dropOf.has(nameOf(n))) { return n; }
        return NO_SYM;
    }

    // The subject of any `subject.$V$k` read, owning payload or not: a binding's store.
    payloadSubject &self inout a:Ast id:NodeId -> Sym {
        if (id == NO_NODE) { return NO_SYM; }
        e: Expr = a.expr(id);
        if (e.op != Op.FieldAccess) { return NO_SYM; }
        p: Payload = e.payload;
        match p {
            Field(f) {
                fn: FieldNode = a.fields.get(f);
                nm: str = nameOf(fn.name);
                if (!isPayloadField(fn.name) || nm == enumTagField()) { return NO_SYM; }
                return self.convBareName(a, fn.base);
            }
            _ { }
        }
        return NO_SYM;
    }

    // Does this store overwrite an owning value, and what says whether that value was live?
    // `guard` names the local whose flag answers, or NO_SYM when the place is always live.
    ownStoreDrop &self inout a:Ast lhs:NodeId -> StoreDrop {
        none: StoreDrop = StoreDrop { needed: false, guard: NO_SYM, structName: NO_SYM };
        e: Expr = a.expr(lhs);
        if (e.kind != Lit.Struct || !gReg.needsDrop(e.structName)) { return none; }
        p: Payload = e.payload;
        match p {
            Name(x) {
                if (e.op != Op.Lvalue) { return none; }
                if (!self.dropOf.has(nameOf(x))) { return none; }   // a global: not tracked
                return StoreDrop { needed: true, guard: x, structName: e.structName };
            }
            _ { }
        }
        root: Sym = self.ownPlaceRoot(a, lhs);
        if (root == NO_SYM) { return none; }
        // A root this function does not track is a borrow whose owner keeps it alive, so the
        // old value is there whatever any flag says.
        g: Sym = NO_SYM;
        if (self.dropOf.has(nameOf(root))) { g = root; }
        return StoreDrop { needed: true, guard: g, structName: e.structName };
    }

    // The variable a field or element chain bottoms out at, refusing a raw-pointer element on
    // the way: nothing releases what a raw pointer reaches, so nothing may release it twice.
    ownPlaceRoot &self inout a:Ast id:NodeId -> Sym {
        cur: NodeId = id;
        while (cur != NO_NODE) {
            e: Expr = a.expr(cur);
            p: Payload = e.payload;
            match p {
                Name(x) { if (e.op == Op.Lvalue) { return x; } return NO_SYM; }
                Field(f) { cur = a.fields.get(f).base; }
                // `*p` of a lent parameter is the place `p` lends (`lendWhole`); a raw pointer's
                // target is nobody's.
                Sub(v) { if (lentPlaceOf(a, cur) == NO_NODE) { return NO_SYM; } cur = v; }
                Index(i) {
                    ix: IndexNode = a.indexes.get(i);
                    if (ix.rawPointerBase) { return NO_SYM; }
                    if (ix.base == NO_NODE) { return ix.name; }
                    cur = ix.base;
                }
                _ { return NO_SYM; }
            }
        }
        return NO_SYM;
    }

    // `__old_N: T; __old_N = <place>;` before the store. NO_SYM when the place cannot be named
    // a second time without evaluating it twice, which is a leak rather than a double release.
    ownSaveOld &self inout a:Ast inout out:Vec<long> lhs:NodeId sn:Sym -> Sym {
        copy: NodeId = self.ownClonePlace(a, out, lhs);
        if (copy == NO_NODE) { return NO_SYM; }
        t: Sym = internString(format("__old{}", self.ownSeq));
        self.ownSeq = self.ownSeq + 1;
        a.decls.push(VarDeclNode { name: t, kind: Lit.Struct, structName: sn,
                                   isArray: false, count: 0, conv: Conv.None, isVariadic: false,
                                   elemKind: Lit.Void, elemStruct: NO_SYM, init: copy });
        out.push(a.addStmt(StmtKind.VarDecl, a.decls.len() - 1));
        return t;
    }

    // A second reading of the same place, so the saved copy and the real store each carry their
    // own nodes. An index that is not already a name or a literal would be evaluated twice, so
    // that place is declined rather than duplicated.
    ownClonePlace &self inout a:Ast inout out:Vec<long> id:NodeId -> NodeId {
        e: Expr = a.expr(id);
        p: Payload = e.payload;
        match p {
            Name(x) {
                if (e.op != Op.Lvalue) { return NO_NODE; }
                return a.leafOf(Op.Lvalue, Payload.Name(x), e.kind, e.structName);
            }
            Sub(v) {
                if (lentPlaceOf(a, id) == NO_NODE) { return NO_NODE; }
                b: NodeId = self.ownClonePlace(a, out, v);
                if (b == NO_NODE) { return NO_NODE; }
                return a.leafOf(Op.Deref, Payload.Sub(b), e.kind, e.structName);
            }
            Field(f) {
                fn: FieldNode = a.fields.get(f);
                b: NodeId = self.ownClonePlace(a, out, fn.base);
                if (b == NO_NODE) { return NO_NODE; }
                a.fields.push(FieldNode { base: b, name: fn.name });
                return a.leafOf(Op.FieldAccess, Payload.Field(a.fields.len() - 1),
                                e.kind, e.structName);
            }
            Index(i) {
                ix: IndexNode = a.indexes.get(i);
                if (ix.whole || ix.index == NO_NODE) { return NO_NODE; }
                // An index that is more than a name or a literal is hoisted into a temporary
                // first, in the real store as well, so the place can be named twice while what
                // selects it is still evaluated once.
                if (!self.ownIsSimple(a, ix.index)) {
                    t: Sym = internString(format("__ix{}", self.ownSeq));
                    self.ownSeq = self.ownSeq + 1;
                    a.decls.push(VarDeclNode { name: t, kind: Lit.Long, structName: NO_SYM,
                                               isArray: false, count: 0, conv: Conv.None,
                                               isVariadic: false, elemKind: Lit.Void,
                                               elemStruct: NO_SYM, init: ix.index });
                    out.push(a.addStmt(StmtKind.VarDecl, a.decls.len() - 1));
                    a.indexes.set(i, IndexNode { name: ix.name, base: ix.base,
                                                 index: a.leafOf(Op.Lvalue, Payload.Name(t),
                                                                 Lit.Long, NO_SYM),
                                                 whole: ix.whole,
                                                 rawPointerBase: ix.rawPointerBase,
                                                 sliceStart: ix.sliceStart, sliceEnd: ix.sliceEnd,
                                                 at: ix.at });
                    ix = a.indexes.get(i);
                }
                b: NodeId = NO_NODE;
                if (ix.base != NO_NODE) {
                    b = self.ownClonePlace(a, out, ix.base);
                    if (b == NO_NODE) { return NO_NODE; }
                }
                ie: Expr = a.expr(ix.index);
                a.indexes.push(IndexNode { name: ix.name, base: b,
                                           index: a.addExpr(ie), whole: false,
                                           rawPointerBase: ix.rawPointerBase,
                                           sliceStart: NO_NODE, sliceEnd: NO_NODE, at: ix.at });
                return a.leafOf(Op.ArrayIndex, Payload.Index(a.indexes.len() - 1),
                                e.kind, e.structName);
            }
            _ { }
        }
        return NO_NODE;
    }

    // ─── parameter conventions ───────────────────────────────────────────────
    //
    // Every struct parameter is either a borrow the callee only reads or a value it takes. An
    // unannotated one is a borrow unless the body writes it, takes its address, or hands the
    // value on (for a type that owns something, handing it on makes its release somebody else's
    // business). Which of the two it is tells the ownership walk whether an argument is moved at
    // a call.
    //
    // A fixpoint, because a bare pass consumes only if that parameter turns out to consume; the
    // demotion is monotone, so it settles.
    inferConventions &self inout a:Ast page:long -> void {
        // A dependency's conventions were settled by its own compile: they are the call ABI
        // its object was built with, so they are taken, not inferred again. Before the fixpoint,
        // because this package's own parameters are decided against them.
        self.applyExternConventions(a, page);
        changed: bool = true;
        rounds: long = 0;
        while (changed && rounds < MAX_CONV_ROUNDS) {
            changed = false;
            n: long = a.blockLen(page);
            for k in 0..n {
                st: Stmt = a.stmtAt(page, k);
                if (st.kind == StmtKind.FunctionDef && !a.fns.get(st.at).isTemplate
                && a.fns.get(st.at).body >= 0 && !isExternFn(st.at) && !isUnchecked(st.at)) {
                    gPos = a.stmtPos.get(a.stmtIdAt(page, k));
                    if (self.inferOne(a, st.at)) { changed = true; }
                }
            }
            rounds = rounds + 1;
        }
        // Everything still undecided only ever read its parameter: it borrows.
        n: long = a.blockLen(page);
        k: long = 0;
        while (k < n) {
            st: Stmt = a.stmtAt(page, k);
            // A template is a pattern and a bodyless declaration is another object's; a
            // convention is inferred from a body, and neither has one. Nor is a dependency's
            // inferred here: `applyExternConventions` already gave it its own.
            if (st.kind != StmtKind.FunctionDef || a.fns.get(st.at).body < 0 || isExternFn(st.at) || isUnchecked(st.at)) { k = k + 1; continue; }
            gPos = a.stmtPos.get(a.stmtIdAt(page, k));
            if (!a.fns.get(st.at).isTemplate) { self.checkDeclaredRead(a, st.at); }
            f: FnNode = a.fns.get(st.at);
            for j in 0..f.argCount {
                at: long = a.params.get(f.firstArg + j);
                p: VarDeclNode = a.decls.get(at);
                // An explicit `read` is the same borrow as an inferred one, and is retyped with
                // it: the convention is spelled either way, and the representation follows.
                if (self.convCandidate(p) && (p.conv == Conv.None || p.conv == Conv.Read)) {
                    self.setConv(a, at, Conv.Read);
                    self.borrowParam(a, at, f.body);
                }
            }
            k = k + 1;
        }
        // Last, with every convention decided and every read parameter now the borrow it is: the
        // callers, held to what each callee turned out to say.
        for k in 0..n {
            st: Stmt = a.stmtAt(page, k);
            if (st.kind == StmtKind.FunctionDef && !a.fns.get(st.at).isTemplate
                && a.fns.get(st.at).body >= 0 && !isExternFn(st.at) && !isUnchecked(st.at)) {
                gPos = a.stmtPos.get(a.stmtIdAt(page, k));
                self.enforceOne(a, st.at);
            }
        }
        // And every `&f` a global holds (`gF: fn(Res)->long = &stash`), which no body reaches.
        for k in 0..self.globalFnRefs.len() {
            id: NodeId = self.globalFnRefs.get(k);
            gPos = self.globalFnRefPos.get(k);
            self.enforceFnRef(a, id, a.expr(id).structName);
        }
    }

    // Every dependency function's parameters as its own compile left them: the convention, and
    // a read struct parameter retyped to the borrow it is. Its body is restamped to match only
    // when it was checked here, for the evaluator; otherwise nothing reads it.
    applyExternConventions &self inout a:Ast page:long -> void {
        n: long = a.blockLen(page);
        for k in 0..n {
            st: Stmt = a.stmtAt(page, k);
            if (st.kind != StmtKind.FunctionDef || !isExternFn(st.at)) { continue; }
            f: FnNode = a.fns.get(st.at);
            fi: long = fnFactOf(st.at);
            if (fi < 0) {
                failStr(format("`{}` comes from a `.klib` that records nothing about it\nnote: the archive is damaged, or was built by a different compiler\nhelp: rebuild it",
                               nameOf(f.name)));
            }
            fact: FnFact = gFacts.fns.get(fi);
            if (fact.paramCount != f.argCount) {
                failStr(format("the `.klib` that declares `{}` is stale: the function has {} here, and {} in the archive\nhelp: rebuild it",
                               nameOf(f.name), plural(f.argCount, "parameter"), fact.paramCount));
            }
            for j in 0..f.argCount {
                at: long = a.params.get(f.firstArg + j);
                p: VarDeclNode = a.decls.get(at);
                pf: ParamFact = gFacts.paramAt(fact, j);
                if (p.conv != pf.conv) { self.setConv(a, at, pf.conv); }
                if (p.kind == Lit.Struct && pf.kind == Lit.Ref) {
                    if (isExternReady(st.at)) { self.borrowParam(a, at, f.body); }
                    else { self.borrowParam(a, at, -1); }
                }
            }
        }
    }

    // What `assert!` calls when it fails (`$panic`, which no source can spell): the function the
    // program marks `@panic`, or NO_SYM when it marks none (an `assert!` is then refused where it
    // stands).
    panicTarget &self inout a:Ast -> Sym {
        if (!gPanicScanned) {
            gPanicScanned = true;
            for i in 0..a.fns.len() {
                f: FnNode = a.fns.get(i);
                if ((f.attrs & FN_PANIC) == 0) { continue; }
                if (gPanicFn != NO_SYM && gPanicFn != f.name) {
                    failStr(format("two functions are marked `@panic`: `{}` and `{}`", nameOf(gPanicFn), nameOf(f.name)));
                }
                gPanicFn = f.name;
            }
        }
        return gPanicFn;
    }

    // The function a `recover` statement links and unlinks its record with: the one the program
    // marks `@recover`, or NO_SYM when it marks none.
    recoverTarget &self inout a:Ast -> Sym {
        if (!gRecoverScanned) {
            gRecoverScanned = true;
            for i in 0..a.fns.len() {
                f: FnNode = a.fns.get(i);
                if ((f.attrs & FN_RECOVER) == 0) { continue; }
                if (gRecoverFn != NO_SYM && gRecoverFn != f.name) {
                    failStr(format("two functions are marked `@recover`: `{}` and `{}`", nameOf(gRecoverFn), nameOf(f.name)));
                }
                gRecoverFn = f.name;
            }
        }
        return gRecoverFn;
    }

    // What a declaration says beyond its signature, held once over the whole program: a raw
    // syscall is `unsafe` (it may write anywhere), and one function at most is `@panic`, and one
    // `@recover`.
    holdDeclarations &self inout a:Ast -> void {
        for i in 0..a.fns.len() {
            f: FnNode = a.fns.get(i);
            if (builtinOf(f) == BI_SYSCALL && !f.isUnsafe) {
                self.atFn(a, i);
                failStr(stringOf("`builtin syscall` must be declared `unsafe`\nnote: a raw syscall may write anywhere\nhelp: declare it as `pub unsafe builtin syscall nr:long args:...long -> long;`"));
            }
            if (isAtomicBuiltin(builtinOf(f)) && !f.isUnsafe) {
                self.atFn(a, i);
                failStr(format("`builtin {}` must be declared `unsafe`\nnote: an atomic reads or writes the word at the raw address it is handed\nhelp: declare it `pub unsafe builtin {} ...;`",
                               lastComponentOf(nameOf(f.name)), lastComponentOf(nameOf(f.name))));
            }
            if (builtinOf(f) == BI_MEMCPY && !f.isUnsafe) {
                self.atFn(a, i);
                failStr(stringOf("`builtin memcpy` must be declared `unsafe`\nnote: it reads and writes the bytes at the raw addresses it is handed\nhelp: declare it as `pub unsafe builtin memcpy dst:long src:long n:long -> void;`"));
            }
        }
        self.panicTarget(a);
        self.recoverTarget(a);
    }

    // Whether `name` never returns, as the settled program decided. What a package build writes
    // into its facts.
    isDivergingFn &self name:Sym -> bool { return self.diverging.has(nameOf(name)); }

    // `read` written by hand is a promise, and this is where it is kept. Inference decides what an
    // unannotated parameter does; an annotated one has already said, so the same facts are read
    // back the other way: a body that writes the value, or hands it on to something that takes
    // it, has broken the contract its own signature offered every caller.
    //
    // Run after the fixpoint, because what a call does to an argument depends on what that callee
    // was inferred to do with its own parameter.
    checkDeclaredRead &self inout a:Ast at:long -> void {
        f: FnNode = a.fns.get(at);
        self.convIdx.clear();
        facts: Vec<long>;
        for k in 0..f.argCount {
            p: VarDeclNode = a.paramAt(f, k);
            facts.push(0);
            if (self.convCandidate(p) && p.conv == Conv.Read) {
                self.convIdx.put(nameOf(p.name), k);
            }
        }
        if (self.convIdx.len() == 0) { return; }
        self.convBlock(a, f.body, &facts);
        for k in 0..f.argCount {
            p: VarDeclNode = a.paramAt(f, k);
            if (self.convCandidate(p) && p.conv == Conv.Read) {
                fl: long = facts.get(k);
                if ((fl & CONV_FORCED) != 0) {
                    failStr(format("parameter `{}` of `{}` is declared `read`, but the body writes it",
                                   nameOf(p.name), nameOf(f.name)));
                }
                if ((fl & CONV_GIVEN) != 0) {
                    failStr(format("parameter `{}` of `{}` is declared `read`, but the body moves it out",
                                   nameOf(p.name), nameOf(f.name)));
                }
            }
        }
    }

    // A read-only struct parameter is a borrow, so it is retyped to one: `Ref` is the borrow
    // representation, a pointer with no callee copy. Nothing downstream has to be told about the
    // convention after this: the type carries it, which is why grepping the back end for
    // `Conv::` finds nothing and the borrow still happens.
    //
    // Every mention of the name in the body follows, or half the body would read a struct where
    // its slot now holds a pointer.
    borrowParam &self inout a:Ast at:long body:long -> void {
        d: VarDeclNode = a.decls.get(at);
        if (d.kind != Lit.Struct) { return; }
        d.kind = Lit.Ref;
        a.decls.set(at, d);
        restampBlock(a, body, d.name);
    }

    convCandidate &self p:VarDeclNode -> bool {
        if (p.kind != Lit.Struct || p.isArray || p.isVariadic) { return false; }
        // A backed enum wears `Lit.Struct` only because the parser gives that kind to every named
        // type it does not otherwise recognise. Its values are its backing integer: there is
        // nothing in memory to borrow, and retyping it to `Ref` would leave the callee reading a
        // pointer where an integer was passed. It would also make `self.take(self.k)` read as
        // `self` lent mutably while `self.k` is also accessed, when it is one value being copied,
        // not two views of it.
        if (p.structName != NO_SYM) {
            named: str = nameOf(p.structName);
            if (gReg.isEnumType(named) && !gReg.isSumType(named)) { return false; }
        }
        return true;
    }

    setConv &self inout a:Ast at:long c:Conv -> void {
        p: VarDeclNode = a.decls.get(at);
        p.conv = c;
        a.decls.set(at, p);
    }

    inferOne &self inout a:Ast at:long -> bool {
        f: FnNode = a.fns.get(at);
        self.convIdx.clear();
        facts: Vec<long>;
        for k in 0..f.argCount {
            p: VarDeclNode = a.paramAt(f, k);
            facts.push(0);
            if (self.convCandidate(p) && p.conv == Conv.None) { self.convIdx.put(nameOf(p.name), k); }
        }
        if (self.convIdx.len() == 0) { return false; }
        self.convBlock(a, f.body, &facts);
        changed: bool = false;
        for k in 0..f.argCount {
            p: VarDeclNode = a.paramAt(f, k);
            if (self.convCandidate(p) && p.conv == Conv.None) {
                fl: long = facts.get(k);
                demote: bool = (fl & CONV_FORCED) != 0;
                if (!demote && gReg.needsDrop(p.structName) && (fl & CONV_GIVEN) != 0) { demote = true; }
                if (demote) {
                    self.setConv(a, a.params.get(f.firstArg + k), Conv.Sink);
                    changed = true;
                }
            }
        }
        return changed;
    }

    convMark &self inout facts:Vec<long> n:Sym bit:long -> void {
        hit: Option<long> = self.convIdx.find(nameOf(n));
        match hit { Some(i) { facts.set(i, facts.get(i) | bit); } None { } }
    }

    convBlock &self inout a:Ast b:long inout facts:Vec<long> -> void {
        // A function declared and not defined has no body to read a convention out of. Its
        // parameters are whatever it was written with, which is what the other object was
        // compiled against.
        if (b < 0) { return; }
        n: long = a.blockLen(b);
        for k in 0..n {
            w: long = a.enterStmt(a.stmtIdAt(b, k));
            self.convStmt(a, a.stmtAt(b, k), facts);
            gPos = w;
        }
    }

    convStmt &self inout a:Ast st:Stmt inout facts:Vec<long> -> void {
        if (st.kind == StmtKind.VarDecl) {
            d: VarDeclNode = a.decls.get(st.at);
            self.convGiven(a, d.init, facts);
            return;
        }
        if (st.kind == StmtKind.Expr || st.kind == StmtKind.Call) {
            self.convExpr(a, a.exprStmts.get(st.at).value, facts);
            return;
        }
        if (st.kind == StmtKind.Return) {
            self.convGiven(a, a.returns.get(st.at).value, facts);
            return;
        }
        if (st.kind == StmtKind.If) {
            c: long = st.at;
            while (c >= 0) {
                nd: IfNode = a.ifs.get(c);
                self.convExpr(a, nd.cond, facts);
                self.convBlock(a, nd.body, facts);
                c = nd.elseIf;
            }
            return;
        }
        if (st.kind == StmtKind.While || st.kind == StmtKind.Recover) {
            w: WhileNode = a.whiles.get(st.at);
            self.convExpr(a, w.cond, facts);
            self.convBlock(a, w.body, facts);
            if (w.step >= 0) { self.convBlock(a, w.step, facts); }
            return;
        }
        // `unsafe` lifts the raw-operation gate, and the enforcement walk rides this one, so the
        // region has to be tracked here as well. It does not lift the contract a callee wrote
        // down: an `inout` parameter still needs its `&` inside one.
        if (st.kind == StmtKind.Unsafe) {
            self.unsafeDepth = self.unsafeDepth + 1;
            self.convBlock(a, a.blockStmts.get(st.at).body, facts);
            self.unsafeDepth = self.unsafeDepth - 1;
            return;
        }
        if (st.kind == StmtKind.Loop || st.kind == StmtKind.Block) {
            self.convBlock(a, a.blockStmts.get(st.at).body, facts);
            return;
        }
        if (st.kind == StmtKind.With) { self.convBlock(a, a.withs.get(st.at).body, facts); return; }
        if (st.kind == StmtKind.Match) {
            m: MatchNode = a.matches.get(st.at);
            k: long = 0;
            // An arm that binds a payload takes it out of the scrutinee, so matching consumes
            // the value exactly as a return or a store does: whether or not the payload it
            // names is the owning one, because what the arms leave behind is released by the
            // sink's scope exit and by nothing else. `_` binds nothing and leaves the value a
            // borrow, which is the whole of the difference between `takeOut` and `tagOf`.
            binds: bool = false;
            while (k < m.armCount) {
                arm: ArmNode = a.arms.get(m.firstArm + k);
                for j in 0..arm.bindCount {
                    if (nameOf(a.names.get(arm.firstBind + j)) != "_") { binds = true; }
                }
                k = k + 1;
            }
            if (binds) { self.convMark(facts, m.scrutinee, CONV_GIVEN); }
            for k in 0..m.armCount {
                arm: ArmNode = a.arms.get(m.firstArm + k);
                self.convExpr(a, arm.test, facts);
                self.convBlock(a, arm.body, facts);
            }
            return;
        }
        if (st.kind == StmtKind.Destructure) {
            self.convGiven(a, a.destructures.get(st.at).value, facts);
            return;
        }
        if (st.kind == StmtKind.Asm) {
            nd: AsmNode = a.asms.get(st.at);
            for at in 0..nd.pieceCount {
                p: AsmPiece = a.asmPieces.get(nd.firstPiece + at);
                // Raw instructions may write anything they name, so a parameter they touch is
                // no longer read-only.
                if (p.name != NO_SYM) { self.convMark(facts, p.name, CONV_FORCED); }
                self.convGiven(a, p.value, facts);
            }
            return;
        }
    }

    // An expression in a position that takes what it names: an initializer, a returned value,
    // a destructured source. A bare parameter there escapes; anything else is an ordinary read.
    convGiven &self inout a:Ast id:NodeId inout facts:Vec<long> -> void {
        if (id == NO_NODE) { return; }
        n: Sym = self.convBareName(a, id);
        // What a move consumes is not always what it names: `h.r` hands an owned field on, and
        // the resource then belongs to whoever took it, so `h` is what escapes.
        if (n == NO_SYM) { n = self.fieldMoveOf(a, id); }
        if (n != NO_SYM) { self.convMark(facts, n, CONV_GIVEN); }
        self.convExpr(a, id, facts);
    }

    convBareName &self inout a:Ast id:NodeId -> Sym {
        e: Expr = a.expr(id);
        if (e.op != Op.Lvalue) { return NO_SYM; }
        p: Payload = e.payload;
        match p { Name(n) { return n; } _ { } }
        return NO_SYM;
    }

    convExpr &self inout a:Ast id:NodeId inout facts:Vec<long> -> void {
        if (id == NO_NODE) { return; }
        e: Expr = a.expr(id);
        if (e.op == Op.Assignment) {
            r: Sym = self.ownPlaceRoot(a, e.left);
            if (r != NO_SYM) { self.convMark(facts, r, CONV_FORCED); }
            self.convGiven(a, e.right, facts);
            self.convExpr(a, e.left, facts);
            return;
        }
        // `&p`: filled or written through the address, or lent onward as `inout`. Either way
        // the parameter needs a value of its own. `&f` of a function is not that at all: it is a
        // value in its own right, and what it has to answer for is whether the pointer's declared
        // conventions still describe the function now that inference has spoken.
        if (e.op == Op.AddressOf) {
            if (e.kind == Lit.Fn) {
                if (self.enforcing) { self.enforceFnRef(a, id, e.structName); }
            } else {
                p: Payload = e.payload;
                match p {
                    Sub(v) {
                        r: Sym = self.ownPlaceRoot(a, v);
                        if (r != NO_SYM) { self.convMark(facts, r, CONV_FORCED); }
                    }
                    _ { }
                }
            }
        }
        self.convExpr(a, e.left, facts);
        self.convExpr(a, e.right, facts);
        q: Payload = e.payload;
        match q {
            Sub(v)  { self.convExpr(a, v, facts); }
            Field(f) { self.convExpr(a, a.fields.get(f).base, facts); }
            Index(i) {
                ix: IndexNode = a.indexes.get(i);
                self.convExpr(a, ix.base, facts);
                self.convExpr(a, ix.index, facts);
                self.convExpr(a, ix.sliceStart, facts);
                self.convExpr(a, ix.sliceEnd, facts);
            }
            Lit(l) {
                ln: LitNode = a.lits.get(l);
                closure: bool = isClosureStruct(ln.typeName);
                self.convGiven(a, ln.rest, facts);
                k: long = 0;
                while (k < ln.initCount) {
                    iv: InitNode = a.inits.get(ln.firstInit + k);
                    // A closure captures a struct by lending it for the call's duration, not by
                    // storing it: the body writes it only where it says so. Reading that `&` as
                    // an ordinary one would make every capturing closure demote the parameter it
                    // captured to a sink, and a caller that used its own value afterwards would
                    // then be refused a second look at it.
                    if (closure && a.expr(iv.value).op == Op.AddressOf) {
                        n: Sym = self.convLentName(a, iv.value);
                        if (n != NO_SYM) {
                            if (self.capturesMutably(a, ln.typeName, iv.name)) {
                                self.convMark(facts, n, CONV_FORCED);
                            }
                            k = k + 1;
                            continue;
                        }
                    }
                    self.convGiven(a, iv.value, facts);
                    k = k + 1;
                }
            }
            Call(c) { self.convCall(a, c, facts); }
            _ { }
        }
    }

    // The bare variable an `&x` capture lends, or NO_SYM when it lends a place, not a name.
    convLentName &self inout a:Ast id:NodeId -> Sym {
        p: Payload = a.expr(id).payload;
        match p { Sub(v) { return self.convBareName(a, v); } _ { } }
        return NO_SYM;
    }

    // Does the closure body write the capture held in `field`? The parser reads a capture as
    // `__cl.<name>` inside `call`, so the question is whether that place is ever a store target
    // or lent onward with `&`. Memoized: inference re-scans every body once a round, and the
    // answer is a property of the closure rather than of the round.
    capturesMutably &self inout a:Ast s:Sym field:Sym -> bool {
        key: str = keepString(format("{}.{}", nameOf(s), nameOf(field)));
        hit: Option<bool> = self.capMut.find(key);
        match hit { Some(b) { return b; } None { } }
        w: bool = false;
        at: long = self.fnNodeOf(methodSymbol(s, intern("call")));
        if (at >= 0) { w = self.capWriteBlock(a, a.fns.get(at).body, field); }
        self.capMut.put(key, w);
        return w;
    }

    capWriteBlock &self inout a:Ast b:long field:Sym -> bool {
        n: long = a.blockLen(b);
        for k in 0..n {
            if (self.capWriteStmt(a, a.stmtAt(b, k), field)) { return true; }
        }
        return false;
    }

    capWriteStmt &self inout a:Ast st:Stmt field:Sym -> bool {
        if (st.kind == StmtKind.VarDecl) { return self.capWriteExpr(a, a.decls.get(st.at).init, field); }
        if (st.kind == StmtKind.Expr || st.kind == StmtKind.Call) {
            return self.capWriteExpr(a, a.exprStmts.get(st.at).value, field);
        }
        if (st.kind == StmtKind.Return) { return self.capWriteExpr(a, a.returns.get(st.at).value, field); }
        if (st.kind == StmtKind.If) {
            c: long = st.at;
            while (c >= 0) {
                nd: IfNode = a.ifs.get(c);
                if (self.capWriteExpr(a, nd.cond, field)) { return true; }
                if (self.capWriteBlock(a, nd.body, field)) { return true; }
                c = nd.elseIf;
            }
            return false;
        }
        if (st.kind == StmtKind.While || st.kind == StmtKind.Recover) {
            w: WhileNode = a.whiles.get(st.at);
            if (self.capWriteExpr(a, w.cond, field)) { return true; }
            if (self.capWriteBlock(a, w.body, field)) { return true; }
            if (w.step >= 0) { return self.capWriteBlock(a, w.step, field); }
            return false;
        }
        if (st.kind == StmtKind.Loop || st.kind == StmtKind.Unsafe || st.kind == StmtKind.Block) {
            return self.capWriteBlock(a, a.blockStmts.get(st.at).body, field);
        }
        if (st.kind == StmtKind.With) { return self.capWriteBlock(a, a.withs.get(st.at).body, field); }
        if (st.kind == StmtKind.Match) {
            m: MatchNode = a.matches.get(st.at);
            for k in 0..m.armCount {
                if (self.capWriteBlock(a, a.arms.get(m.firstArm + k).body, field)) { return true; }
            }
            return false;
        }
        return false;
    }

    capWriteExpr &self inout a:Ast id:NodeId field:Sym -> bool {
        if (id == NO_NODE) { return false; }
        e: Expr = a.expr(id);
        if (e.op == Op.Assignment && self.namesCapture(a, e.left, field)) { return true; }
        if (e.op == Op.AddressOf) {
            p: Payload = e.payload;
            match p { Sub(v) { if (self.namesCapture(a, v, field)) { return true; } } _ { } }
        }
        if (self.capWriteExpr(a, e.left, field)) { return true; }
        if (self.capWriteExpr(a, e.right, field)) { return true; }
        q: Payload = e.payload;
        match q {
            Sub(v)   { return self.capWriteExpr(a, v, field); }
            Field(f) { return self.capWriteExpr(a, a.fields.get(f).base, field); }
            Index(i) {
                ix: IndexNode = a.indexes.get(i);
                if (self.capWriteExpr(a, ix.base, field)) { return true; }
                return self.capWriteExpr(a, ix.index, field);
            }
            Lit(l) {
                ln: LitNode = a.lits.get(l);
                for k in 0..ln.initCount {
                    if (self.capWriteExpr(a, a.inits.get(ln.firstInit + k).value, field)) { return true; }
                }
                return false;
            }
            Call(c) {
                cn: CallNode = a.calls.get(c);
                if (self.capWriteExpr(a, cn.receiver, field)) { return true; }
                for k in 0..cn.argCount {
                    if (self.capWriteExpr(a, a.argAt(cn, k), field)) { return true; }
                }
                return false;
            }
            _ { }
        }
        return false;
    }

    // Is this place rooted at the capture `__cl.<field>`?
    namesCapture &self inout a:Ast id:NodeId field:Sym -> bool {
        cur: NodeId = id;
        while (cur != NO_NODE) {
            e: Expr = a.expr(cur);
            p: Payload = e.payload;
            match p {
                Field(f) {
                    fn: FieldNode = a.fields.get(f);
                    if (fn.name == field && self.convBareName(a, fn.base) == intern("__cl")) {
                        return true;
                    }
                    cur = fn.base;
                }
                Index(i) { cur = a.indexes.get(i).base; }
                // `*__cl.t = v`, a captured struct written whole (`lendWhole`).
                Sub(v) { if (lentPlaceOf(a, cur) == NO_NODE) { return false; } cur = v; }
                _ { return false; }
            }
        }
        return false;
    }

    convCall &self inout a:Ast c:long inout facts:Vec<long> -> void {
        cn: CallNode = a.calls.get(c);
        self.convExpr(a, cn.receiver, facts);
        self.convExpr(a, cn.callee, facts);
        at: long = self.fnNodeOf(cn.name);
        base: long = 0;
        if (cn.receiver != NO_NODE) {
            base = 1;
            r: Sym = self.convBareName(a, cn.receiver);
            if (r == NO_SYM) { r = self.fieldMoveOf(a, cn.receiver); }   // `h.r.consume()` gives `h` up
            if (r != NO_SYM && self.convGives(a, at, cn, 0)) { self.convMark(facts, r, CONV_GIVEN); }
        }
        for k in 0..cn.argCount {
            arg: NodeId = a.argAt(cn, k);
            n: Sym = self.convBareName(a, arg);
            // A parameter handed on by value takes the caller's own too: `feed s:Sink r:Res`
            // whose body writes `s.swallow(r)` cannot declare `r` read, and through a trait
            // object the trait's signature is the only thing that says so. So does a field of it
            // handed on (`eat(h.r)`), as a store of one does (`convGiven`): `h` must be the
            // function's own for the field to be taken out of it.
            if (n == NO_SYM) { n = self.fieldMoveOf(a, arg); }
            if (n != NO_SYM && self.convGives(a, at, cn, base + k)) { self.convMark(facts, n, CONV_GIVEN); }
            self.convExpr(a, arg, facts);
        }
        if (self.enforcing) { self.enforceCallSite(a, c, at); }
    }

    // `&x` is how safe code lends, and the two halves of that are one rule: an `inout` parameter
    // may only be reached with a `&`, because mutation through a call has to be visible where the
    // call is written and not only where the callee is; and a `&` anywhere else is a mistake,
    // because safe code has no other use for an address. A method's receiver is exempt. It lends
    // without saying so, there being nowhere else for a receiver to come from.
    enforceCallSite &self inout a:Ast c:long at:long -> void {
        if (at < 0) { return; }
        cn: CallNode = a.calls.get(c);
        if (cn.slot != NO_SLOT) { return; }        // through a value: no declaration to read
        f: FnNode = a.fns.get(at);
        base: long = 0;
        if (cn.receiver != NO_NODE) { base = 1; }
        for k in 0..cn.argCount {
            i: long = base + k;
            if (i >= f.argCount) { return; }
            p: VarDeclNode = a.paramAt(f, i);
            if (p.isVariadic) { return; }          // the tail is one slice the call built
            arg: NodeId = a.argAt(cn, k);
            lend: bool = self.isLend(a, arg);
            // An `inout` scalar: `&n` lends a local (or field, or element); a parameter that is
            // itself an `inout` scalar is forwarded as it is, `x` or `&x`.
            if (p.conv == Conv.Inout && p.kind == Lit.Ref && isInoutScalarName(p.structName)) {
                ae: Expr = a.expr(arg);
                if (ae.op == Op.AddressOf) { continue; }
                if (ae.op == Op.Deref && lentPlaceOf(a, arg) != NO_NODE) {
                    a.setExpr(arg, a.expr(lentPlaceOf(a, arg)));
                    continue;
                }
                failStr(format("parameter {} of `{}` is an `inout` scalar, and this argument is not lent\nhelp: lend it with `&`, as in `{}(&n)`",
                               i, nameOf(f.name), nameOf(f.name)));
            }
            if (p.conv == Conv.Inout) {
                if (!lend) { self.enforceInoutArg(a, arg, i, f.name); }
            } else if (lend && self.unsafeDepth == 0) {
                // `&x` to a parameter that reads is the borrow passing already is: the `&` goes.
                // To one that takes the value it would lend what the callee then owns.
                if (p.conv == Conv.Sink) {
                    failStr(format("cannot lend an argument to parameter {} of `{}`, which takes it\nnote: the parameter is a `sink`, and `&` lends\nhelp: pass the value itself to hand it over, or clone it",
                                   i, nameOf(f.name)));
                }
                self.dropLend(a, arg);
            }
        }
    }

    // The `&n` of a scalar this call's arguments took (from `mark` on): each must stand for an
    // `inout` parameter of exactly its type, or it is the raw address `unsafe` alone may take.
    holdScalarLends &self inout a:Ast cn:CallNode fn:Sym tmpl:Sym base:long mark:long -> void {
        if (self.scalarLends.len() <= mark) { return; }
        at: long = self.fnNodeOf(fn);
        // A generic function's instance may not be stamped yet: its template says the same.
        if (at < 0) {
            for i in 0..a.fns.len() { if (a.fns.get(i).name == tmpl) { at = i; } }
        }
        for k in 0..cn.argCount {
            arg: NodeId = a.argAt(cn, k);
            mine: bool = false;
            for j in mark..self.scalarLends.len() { if (self.scalarLends.get(j) == arg) { mine = true; } }
            if (!mine) { continue; }
            p: VarDeclNode = VarDeclNode { name: NO_SYM, kind: Lit.Void, structName: NO_SYM, isArray: false, count: 0,
                                           conv: Conv.None, isVariadic: false, elemKind: Lit.Void,
                                           elemStruct: NO_SYM, init: NO_NODE };
            if (at >= 0 && base + k < a.fns.get(at).argCount) { p = a.paramAt(a.fns.get(at), base + k); }
            if (p.conv != Conv.Inout || p.kind != Lit.Ref || !isInoutScalarName(p.structName)) {
                self.requireUnsafe("taking a raw address with `&`");
                continue;
            }
            self.holdLend(a, arg, p, fn, base + k);
        }
        while (self.scalarLends.len() > mark) { self.scalarLends.pop(); }
    }

    // `&n` lent to the `inout` scalar parameter `p`: of exactly its type.
    holdLend &self inout a:Ast arg:NodeId p:VarDeclNode fn:Sym pos:long -> void {
        want: TypeRef = inoutScalarOf(p.structName);
        got: Expr = a.expr(self.subOf(a, arg));
        gk: Lit = got.kind;
        gn: Sym = got.structName;
        if (!namedScalar(gk, gn)) { gn = NO_SYM; }
        wn: Sym = want.name;
        if (!namedScalar(want.base, wn)) { wn = NO_SYM; }
        if (gk != want.base || gn != wn) {
            failStr(format("mismatched types: expected `{}`, found `{}`\nnote: parameter `{}` of `{}` is `inout` with type `{}`, and a lend must be of exactly the parameter's type",
                           self.spellType(want.base, wn), self.spellType(gk, gn), nameOf(p.name), nameOf(fn), self.spellType(want.base, wn)));
        }
    }
    forgetScalarLend &self arg:NodeId -> void {
        k: long = 0;
        while (k < self.scalarLends.len()) {
            if (self.scalarLends.get(k) == arg) { self.scalarLends.removeAt(k); } else { k = k + 1; }
        }
    }

    subOf &self inout a:Ast id:NodeId -> NodeId {
        p: Payload = a.expr(id).payload;
        match p { Sub(v) { return v; } _ { } }
        return id;
    }

    // `&x` handed to a parameter that only reads: the argument is `x`, the borrow passing a struct
    // already is.
    dropLend &self inout a:Ast arg:NodeId -> void {
        e: Expr = a.expr(arg);
        p: Payload = e.payload;
        match p { Sub(v) { ne: Expr = a.expr(v); ne.isParen = e.isParen; a.setExpr(arg, ne); } _ { } }
    }

    // Before the arguments are held to the callee: a `&x` handed to a parameter declared a borrow
    // (`r:&T`) is `x`. Done here rather than when conventions are settled, so the caller's own
    // conventions are inferred from what the call does (reads), not from the `&`.
    dropReadLends &self inout a:Ast cn:CallNode fn:Sym base:long -> void {
        any: bool = false;
        for k in 0..cn.argCount { if (a.expr(a.argAt(cn, k)).op == Op.AddressOf) { any = true; } }
        if (!any) { return; }
        at: long = self.fnNodeOf(fn);
        if (at < 0 || self.unsafeDepth > 0) { return; }
        f: FnNode = a.fns.get(at);
        for k in 0..cn.argCount {
            if (base + k >= f.argCount) { return; }
            p: VarDeclNode = a.paramAt(f, base + k);
            if (p.isVariadic) { return; }
            if (p.kind == Lit.Ref && p.conv != Conv.Inout && self.isLend(a, a.argAt(cn, k))) {
                self.dropLend(a, a.argAt(cn, k));
            }
        }
    }

    // `&x` in the lending sense: the address of something that lives in memory. `&f` is a
    // function pointer and `&n` of a scalar is a raw address; neither lends anything.
    isLend &self inout a:Ast id:NodeId -> bool {
        if (id == NO_NODE) { return false; }
        e: Expr = a.expr(id);
        if (e.op != Op.AddressOf || e.kind == Lit.Fn) { return false; }
        p: Payload = e.payload;
        inner: NodeId = NO_NODE;
        match p { Sub(v) { inner = v; } _ { return false; } }
        if (inner == NO_NODE) { return false; }
        t: Lit = a.expr(inner).kind;
        return t == Lit.Struct || t == Lit.Ref || t == Lit.Slice;
    }

    // An `inout` argument that is not a lend. Forwarding a borrow this function was itself handed
    // is the one other thing it may be, and only a mutable one: a read borrow lent onward as
    // `inout` would let the callee write through a promise that it would not.
    enforceInoutArg &self inout a:Ast arg:NodeId i:long callee:Sym -> void {
        // A borrow a call returned (`take(xs.at(0))`, `f(m.get(k))`) is already the lend. The
        // language lets a returned `&T` be written through and lent on within the expression it
        // came from, and `names[1].pushStr("!")` does exactly that. Only a bare variable carries
        // the read/inout distinction the check below enforces; a returned borrow is as mutable as
        // the receiver it came out of was.
        e: Expr = a.expr(arg);
        if (e.kind == Lit.Ref) {
            p: Payload = e.payload;
            match p { Call(_) { return; } Index(_) { return; } _ { } }
        }
        n: Sym = self.convBareName(a, arg);
        if (n != NO_SYM) {
            t: Lit = a.expr(arg).kind;
            if (t == Lit.Ref || t == Lit.Slice) {
                if (self.paramConvOf(a, self.enforceFn, n) == Conv.Inout) { return; }
                failStr(format("cannot lend `{}` mutably\nnote: it is a read-only borrow, and parameter {} of `{}` is `inout`",
                               nameOf(n), i, nameOf(callee)));
            }
        }
        failStr(format("parameter {} of `{}` is `inout`, and this argument is not lent\nhelp: lend it with `&`, as in `{}(&x)`",
                       i, nameOf(callee), nameOf(callee)));
    }

    paramConvOf &self inout a:Ast at:long n:Sym -> Conv {
        f: FnNode = a.fns.get(at);
        for k in 0..f.argCount {
            p: VarDeclNode = a.paramAt(f, k);
            if (p.name == n) { return p.conv; }
        }
        return Conv.None;
    }

    // One function's call sites, judged. The facts vector is unused (`convIdx` is left empty, so
    // nothing is marked) and the walk is reused whole rather than written a second time: it is
    // already the one place that reaches every statement kind, an `asm` block's inputs included.
    enforceOne &self inout a:Ast at:long -> void {
        f: FnNode = a.fns.get(at);
        self.convIdx.clear();
        facts: Vec<long>;
        for k in 0..f.argCount { facts.push(0); }
        self.enforcing = true;
        self.enforceFn = at;
        self.unsafeDepth = 0;
        if (f.isUnsafe) { self.unsafeDepth = 1; }
        self.convBlock(a, f.body, &facts);
        self.enforcing = false;
        self.unsafeDepth = 0;
    }

    // ─── reading a callee's signature ────────────────────────────────────────

    fnNodeOf &self n:Sym -> long {
        hit: Option<long> = self.fnAt.find(nameOf(n));
        match hit { Some(i) { return i; } None { } }
        return NOT_FOUND;
    }

    // Does parameter `i` of the function at `at` take its argument's value?
    paramConsumes &self inout a:Ast at:long i:long -> bool {
        f: FnNode = a.fns.get(at);
        if (i >= f.argCount) { return false; }
        p: VarDeclNode = a.paramAt(f, i);
        if (!self.convCandidate(p)) { return false; }
        return p.conv != Conv.Read && p.conv != Conv.Inout;
    }

    // The same question for a call the checker resolved to a vtable slot: a trait object's method
    // has no definition at the call site, so there is no function node to read. The trait's own
    // signature is where `r: sink Res` was written, a caller through a trait object sees only
    // the trait, so it is the trait's word that decides whether the argument moves, and anything
    // it does not mark `sink` is lent, unlike an unannotated function parameter whose convention
    // is inferred from its body.
    //
    // The trait's parameter list does not count the receiver, so call index 0 is `self` (never
    // consumed through a trait object: the vtable holds a borrow) and index i is signature i-1.
    dispatchConsumes &self inout a:Ast cn:CallNode i:long -> bool {
        if (cn.slot < 0 || cn.receiver == NO_NODE || i == 0) { return false; }
        r: Expr = a.expr(cn.receiver);
        if (r.kind != Lit.TraitObj || r.structName == NO_SYM) { return false; }
        at: long = gReg.findTraitSym(r.structName);
        if (at < 0) { return false; }
        t: TraitDef = gReg.traitDef(at);
        if (cn.slot >= t.methodCount) { return false; }
        sig: TraitMethodSig = gReg.traitMethodAt(t, cn.slot);
        if (i - 1 >= sig.paramCount) { return false; }
        p: VarDeclNode = a.decls.get(a.params.get(sig.firstParam + i - 1));
        return self.convCandidate(p) && p.conv == Conv.Sink;
    }

    // The same question for a call through a fn value: a fn-typed local, or a fn-typed field.
    // There is no callee definition to read a convention out of; that is what makes the call
    // indirect. The pointer's own type is the whole answer, which is exactly why a fn type has to
    // carry its parameters' conventions: a `sink` parameter takes the argument, and anything else
    // lends it. Without this, the caller would keep a value the callee had already released, and
    // release it a second time.
    //
    // Only an aggregate moves. A scalar handed over is a scalar copied, whatever the word says.
    indirectConsumes &self cn:CallNode i:long -> bool {
        at: long = gFnSigs.find(cn.sigKey);
        if (at < 0) { return false; }
        sig: FnSig = gFnSigs.sigAt(at);
        if (i < 0 || i >= sig.paramCount) { return false; }
        p: FnParam = gFnSigs.paramAt(sig, i);
        if (p.conv != Conv.Sink) { return false; }
        return p.kind == Lit.Struct || p.kind == Lit.Ref;
    }

    // What parameter `i` of a call does to its argument, from whichever signature there is: the
    // pointer's when the call goes through a value, the callee's when it resolved to one, the
    // trait's when it goes through a vtable.
    argConsumes &self inout a:Ast at:long cn:CallNode i:long -> bool {
        if (cn.sigKey != NO_SYM) { return self.indirectConsumes(cn, i); }
        if (at >= 0) { return self.paramConsumes(a, at, i); }
        return self.dispatchConsumes(a, cn, i);
    }

    // The same question while conventions are still being inferred, where only an explicit `sink`
    // counts: an unannotated parameter is what this pass is deciding, and reading one as a give
    // would demote every caller of it in the first round. A fn type is not being inferred (it
    // was written down) so an indirect call answers the same in both rounds.
    convGives &self inout a:Ast at:long cn:CallNode i:long -> bool {
        if (cn.sigKey != NO_SYM) { return self.indirectConsumes(cn, i); }
        if (at < 0) { return self.dispatchConsumes(a, cn, i); }
        f: FnNode = a.fns.get(at);
        if (i >= f.argCount) { return false; }
        return a.paramAt(f, i).conv == Conv.Sink;
    }

    // `&f` was typed by f's declared conventions, so a fn type that says nothing accepted it.
    // Now that inference has decided what f really does with each parameter, the two must agree
    // wherever it matters: a pointer of type `fn(T)` lends its argument, and a callee that
    // consumes it releases what the caller still owns. A type that owns nothing has no release to
    // duplicate, so there the difference is only whether the callee copies, and either is fine.
    enforceFnRef &self inout a:Ast id:NodeId key:Sym -> void {
        sat: long = gFnSigs.find(key);
        if (sat < 0) { return; }
        fn: Sym = self.addressedName(a, id);
        if (fn == NO_SYM) { return; }
        fat: long = self.fnNodeOf(fn);
        if (fat < 0) { return; }
        fd: FnNode = a.fns.get(fat);
        sig: FnSig = gFnSigs.sigAt(sat);
        i: long = 0;
        while (i < sig.paramCount && i < fd.argCount) {
            p: FnParam = gFnSigs.paramAt(sig, i);
            have: Conv = a.paramAt(fd, i).conv;
            at: long = i;
            i = i + 1;
            // A fn type's parameter is lent read-only or given (`sink`); it has no word for a
            // lend the callee writes, so a function that writes one cannot stand behind it: the
            // call `f(p)` would write `p` with nothing at the call to say so, and the guard and
            // the exclusivity check take the fn type at its word. Whatever the type, not only
            // one that owns something.
            if (have == Conv.Inout) {
                failStr(format("cannot use `&{}` as a fn value\nnote: parameter {} of `{}` is `inout`, and a fn type cannot lend a parameter to be written (its parameters are lent read-only or given with `sink`)\nhelp: take the value or a read borrow instead, or call `{}` directly",
                               nameOf(fn), at, nameOf(fn), nameOf(fn)));
            }
            if (p.kind != Lit.Struct && p.kind != Lit.Ref) { continue; }
            if (!gReg.needsDrop(p.name)) { continue; }
            if ((p.conv == Conv.Sink) == (have == Conv.Sink)) { continue; }
            m: String;
            m.pushStr("`&");
            m.pushStr(nameOf(fn));
            m.pushStr("` does not fit `");
            m.pushStr(nameOf(key));
            m.pushStr("`\nnote: parameter ");
            m.pushLong(at);
            m.pushStr(" is ");
            if (have == Conv.Sink) { m.pushStr("consumed"); } else { m.pushStr("borrowed"); }
            m.pushStr(" by `");
            m.pushStr(nameOf(fn));
            m.pushStr("`, but the pointer type says `");
            if (p.conv == Conv.Sink) { m.pushStr("sink"); } else { m.pushStr("read"); }
            m.pushStr("`\nhelp: declare the parameter ");
            if (p.conv == Conv.Sink) { m.pushStr("`sink`"); } else { m.pushStr("`read`"); }
            m.pushStr(", or change the pointer type to `fn(");
            if (have == Conv.Sink) { m.pushStr("sink "); }
            m.pushStr(nameOf(p.name));
            m.pushStr(", ...)`");
            failStr(m);
        }
    }

    // ─── drop glue ───────────────────────────────────────────────────────────
    //
    // A struct that holds something owning must release it, whether or not it wrote a `drop` of
    // its own. The glue is the release nobody wrote: each owning field, in reverse declaration
    // order. A hand-written `drop` runs first, under a private name, as in Rust: the author's
    // release is about what the value holds beyond its fields, not instead of theirs.
    dropGlue &self inout a:Ast page:long -> void {
        extra: Vec<long>;
        for i in 0..gReg.structCount() {
            self.glueFor(a, &extra, gReg.structDef(i));
        }
        if (extra.len() == 0) { return; }
        b: Block = a.blocks.get(page);
        ids: Vec<long>;
        for k in 0..b.stmtCount { ids.push(a.stmtRuns.get(b.firstStmt + k)); }
        ids.extend(extra);
        first: long = a.stmtRuns.len();
        a.stmtRuns.extend(ids);
        a.blocks.set(page, Block { firstStmt: first, stmtCount: ids.len() });
    }

    glueFor &self inout a:Ast inout extra:Vec<long> d:StructDef -> void {
        s: Sym = d.name;
        if (!gReg.needsDrop(s)) { return; }
        owning: long = 0;
        for k in 0..d.fieldCount {
            f: FieldDef = gReg.fieldAt(d, k);
            if (f.kind == Lit.Struct && gReg.needsDrop(f.structName)) { owning = owning + 1; }
        }
        if (owning == 0) { return; }
        own: Sym = methodSymbol(s, intern("drop"));
        userAt: long = self.fnNodeOf(own);
        body: Vec<long>;
        selfName: Sym = intern("self");
        if (userAt >= 0) {
            // The author's own release, kept under a private name; the name every drop site
            // calls is the glue's.
            uf: FnNode = a.fns.get(userAt);
            priv: Sym = internString(format("{}$own", nameOf(own)));
            uf.name = priv;
            a.fns.set(userAt, uf);
            self.fnAt.put(nameOf(priv), userAt);
            self.fnAt.remove(nameOf(own));
            // Its statement is already noted under the old name, and is not walked again.
            self.noteReturn(priv, varType(uf.returnKind, uf.returnStruct));
            recv: NodeId = a.leafOf(Op.Lvalue, Payload.Name(selfName), Lit.Ref, s);
            a.calls.push(CallNode { name: priv, receiver: recv, firstArg: 0, argCount: 0,
                                    slot: NO_SLOT, callee: NO_NODE, sigKey: NO_SYM });
            a.exprStmts.push(ExprStmtNode { value: a.leafOf(Op.MethodCall,
                                                            Payload.Call(a.calls.len() - 1),
                                                            Lit.Void, NO_SYM) });
            body.push(a.addStmt(StmtKind.Expr, a.exprStmts.len() - 1));
        }
        k: long = d.fieldCount;
        while (k > 0) {
            k = k - 1;
            f: FieldDef = gReg.fieldAt(d, k);
            if (!(f.kind == Lit.Struct && gReg.needsDrop(f.structName))) { continue; }
            recv: NodeId = a.leafOf(Op.Lvalue, Payload.Name(selfName), Lit.Ref, s);
            a.fields.push(FieldNode { base: recv, name: f.name });
            fv: NodeId = a.leafOf(Op.FieldAccess, Payload.Field(a.fields.len() - 1),
                                  Lit.Struct, f.structName);
            if (f.isArray) {
                self.elemLoop(a, &body,
                              OwnLocal { name: NO_SYM, structName: f.structName, count: f.count },
                              fv, true);
            }
            else {
                st: long = self.ownDropOf(a, fv, f.structName);
                // Exactly one variant of a sum type is live, so a payload is released only when
                // the tag says it is the one that was built.
                if (d.isEnum) { st = self.tagGuard(a, d, f.name, st); }
                body.push(st);
            }
        }
        a.decls.push(VarDeclNode { name: selfName, kind: Lit.Ref, structName: s,
                                   isArray: false, count: 0, conv: Conv.Inout, isVariadic: false,
                                   elemKind: Lit.Void, elemStruct: NO_SYM, init: NO_NODE });
        params: Vec<long>;
        params.push(a.decls.len() - 1);
        firstArg: long = a.params.len();
        a.params.extend(params);
        a.fns.push(FnNode { name: own, returnKind: Lit.Void, returnStruct: NO_SYM,
                            visibility: Vis.Pub, file: NO_SYM, pkg: NO_SYM,
                            isUnsafe: false, isTemplate: false, inferReturn: false,
                            firstBound: 0, boundCount: 0, firstArg: firstArg,
                            argCount: 1, body: a.addBlock(body) });
        extra.push(a.addStmt(StmtKind.FunctionDef, a.fns.len() - 1));
        self.fnAt.put(nameOf(own), a.fns.len() - 1);
        self.noteReturn(own, varType(Lit.Void, NO_SYM));
        if (userAt < 0) {
            fns: Vec<Sym>;
            fns.push(own);
            gReg.addImpl(s, TraitRef { name: intern("Drop"), firstArg: 0, argCount: 0 }, fns);
        }
    }

    // `if (self.$tag == <variant>) { <release> }` around a sum type's payload release.
    tagGuard &self inout a:Ast d:StructDef field:Sym st:long -> long {
        at: long = gReg.findEnumSym(d.name);
        if (at < 0) { return st; }
        ed: EnumDef = gReg.enumDef(at);
        for k in 0..ed.variantCount {
            v: VariantDef = gReg.variantAt(ed, k);
            for j in 0..v.payloadCount {
                if (enumPayloadField(nameOf(v.name), j) == field) {
                    recv: NodeId = a.leafOf(Op.Lvalue, Payload.Name(intern("self")), Lit.Ref, d.name);
                    a.fields.push(FieldNode { base: recv, name: intern(enumTagField()) });
                    tag: NodeId = a.leafOf(Op.FieldAccess, Payload.Field(a.fields.len() - 1),
                                           ed.backing, NO_SYM);
                    body: Vec<long>;
                    body.push(st);
                    a.ifs.push(IfNode { cond: a.binary(Op.IsEqual, tag,
                                                       a.leaf(Op.Literal, Payload.Num(v.value), ed.backing),
                                                       Lit.Int),
                                        body: a.addBlock(body), elseIf: -1 });
                    return a.addStmt(StmtKind.If, a.ifs.len() - 1);
                }
            }
        }
        return st;
    }
}

// The same node with a different name in its payload.
pub withName e:Expr n:Sym -> Expr {
    out: Expr = e;
    out.payload = Payload.Name(n);
    return out;
}

// A local the compiler declared rather than the author: a `with` guard, a `match`'s hidden
// binding, a `for`'s iterator, a hoisted temporary. Every one is `$`-prefixed, and rules written
// for what someone wrote should not be applied to what the desugars build.
pub isTempName n:Sym -> bool {
    if (n == NO_SYM) { return false; }
    s: str = lastComponentOf(nameOf(n));
    return s.len > 0 && charAt(s, 0) == '$';
}

// A capture struct the parser desugared a closure literal into, or an instance of a generic one.
// The registry says so (`Registry.isClosureEnv`); the spelling cannot. An instance parameterized
// by a closure (`Keep<$closure0>`, mangled `Keep_mod::$closure0`) names one without being one,
// and a closure's own instance at a struct ends with that struct's name (`m::$closure0_7_m::P`).
pub isClosureStruct n:Sym -> bool { return gReg.isClosureEnv(n); }

// Does `==` on this operand mean a call rather than a machine comparison? Every value in memory
// does (the hardware cannot compare a block of bytes) with one exception the kind alone cannot
// see: the parser gives every named type it does not otherwise recognise `Lit.Struct`, and a
// backed enum is one of those. `config == BufWriterConfig.LineBuffered` compares two integers.
pub comparedByCall t:VarType -> bool {
    if (!isAggregate(t.kind)) { return false; }
    if (t.kind == Lit.Struct && t.structName != NO_SYM) {
        q: str = nameOf(t.structName);
        // A distinct type is an integer underneath, and has the base's comparisons only where it
        // implements them: `==` means its `Eq`, `<` its `Ord`, like an aggregate's.
        if (gReg.isEnumType(q) && !gReg.isSumType(q)) { return gReg.isDistinct(t.structName); }
    }
    return true;
}

// What an operator on a borrow works on: the value it borrows. `w == "x"` with `w: &String` is
// String's `Eq<str>`, `a < b` with two `&P` is P's `Ord`, `a + b` P's `Add<P>`; the call lends
// the borrow on as the `&self` (or the argument) it already is. A borrow of a scalar is the
// scalar; an `inout` scalar's lend is left as it is.
pub underBorrow t:VarType -> VarType {
    if (t.kind != Lit.Ref || t.structName == NO_SYM || t.isArray || isInoutScalarName(t.structName)) { return t; }
    q: str = nameOf(t.structName);
    if (namesScalar(q)) { return varType(scalarNamed(q), NO_SYM); }
    return varType(Lit.Struct, t.structName);
}

// For a refusal about an operator on a distinct type: a `note:` line saying why it has none and
// the two ways out, or "". It starts with a newline, so it goes right after the message's first
// line, ahead of the `help:`.
pub distinctHint t:VarType -> str {
    if (t.kind != Lit.Struct || !gReg.isDistinct(t.structName)) { return ""; }
    b: TypeRef = gReg.distinctOf(t.structName);
    return keepString(format("\nnote: `{}` is a distinct `{}`, so it has an operator only where it implements the operator's trait, or once converted with `x as {}`",
                             nameOf(t.structName), typeMangleName(b.base, b.name), typeMangleName(b.base, b.name)));
}

// The `call` method a closure literal was desugared into: `methodName(owner, call)` of a capture
// struct, so the owner is the name less `_call`, and the registry answers for the owner.
pub isClosureCall n:Sym -> bool {
    if (n == NO_SYM) { return false; }
    s: str = nameOf(n);
    if (!strEndsWith(s, "_call")) { return false; }
    return gReg.isClosureEnv(symIfAny(strSlice(s, 0, s.len - 5)));
}

// The trait an arithmetic operator on an aggregate means, or "" for an operator that has none and
// so stays the machine operation it is. The METHOD is this name in lower case, so the pairing is
// not a second table that could disagree with this one.
pub opTraitName op:Op -> str {
    if (op == Op.Addition)       { return "Add"; }
    if (op == Op.Subtraction)    { return "Sub"; }
    if (op == Op.Multiplication) { return "Mul"; }
    if (op == Op.Division)       { return "Div"; }
    if (op == Op.Modulus)        { return "Rem"; }
    if (op == Op.BitwiseAnd)     { return "BitAnd"; }
    if (op == Op.BitwiseOr)      { return "BitOr"; }
    if (op == Op.BitwiseXor)     { return "BitXor"; }
    if (op == Op.ShiftLeft)      { return "Shl"; }
    if (op == Op.ShiftRight)     { return "Shr"; }
    return "";
}

pub lowerOf s:str -> str {
    out: String;
    for i in 0..s.len { out.push(toLower(charAt(s, i)) as char); }
    return keepString(out);
}


// `T_method`: the ordinary function a method call resolves to.
pub methodSymbol owner:Sym method:Sym -> Sym {
    s: String;
    s.pushStr(nameOf(owner));
    s.push('_');
    s.pushStr(nameOf(method));
    out: Sym = NO_SYM;
    out = internString(s);
    return out;
}

// ─── macros ──────────────────────────────────────────────────────────────────
//
// `m!(args)` is expanded here, while the caller is being checked, because that is the one
// moment the caller's scope is exactly right for what the macro produces: a `Node` result is
// turned back into syntax, put where the call was, and checked like anything hand-written.
// The macro itself runs in the evaluator, on its arguments: for a parameter of type `Node`
// the argument's tree, quoted; for anything else, a value the compiler can compute.
//
// A macro can run only once its body and everything that body calls are checked (the
// evaluator reads typed trees), so a function that invokes a macro not yet ready is held
// back and retried the next round, after the driver has stamped what the macro needs.

methods Checker {
    // Whether every macro a body invokes can run now.
    macrosReady &self inout a:Ast b:long -> bool {
        calls: Vec<Sym>;
        self.macroCallsIn(a, b, &calls);
        for k in 0..calls.len() {
            if (!self.macroRunnable(a, calls.get(k))) { return false; }
        }
        return true;
    }
    exprMacrosReady &self inout a:Ast id:NodeId -> bool {
        calls: Vec<Sym>;
        self.namesInExpr(a, id, &calls, true);
        for k in 0..calls.len() {
            if (!self.macroRunnable(a, calls.get(k))) { return false; }
        }
        return true;
    }
    macroRunnable &self inout a:Ast bare:Sym -> bool {
        q: Sym = self.resolveFn(bare);
        // Once runnable, always: what it reaches stays checked.
        if (self.macroOk.has(nameOf(q))) { return true; }
        hit: Option<long> = self.fnAt.find(nameOf(q));
        at: long = -1;
        match hit { Some(i) { at = i; } None { } }
        if (at < 0 || !gReg.isMacro(q)) { return true; }    // not a macro at all: the expansion will say so
        seen: HashMap<str, bool>;
        self.initSeen.clear();
        if (!self.bodyReady(a, at, &seen, bare)) { return false; }
        self.macroOk.put(nameOf(q), true);
        return true;
    }
    // A function and, transitively, what its typed body calls: all checked, all stamped.
    bodyReady &self inout a:Ast at:long inout seen:HashMap<str, bool> m:Sym -> bool {
        f: FnNode = a.fns.get(at);
        if (seen.has(nameOf(f.name))) { return true; }
        seen.put(nameOf(f.name), true);
        // A `builtin`: the compiler provides it, and there is no body to wait for.
        if (builtinOf(f) != 0) { return true; }
        if (!self.fnDone.has(nameOf(f.name))) {
            // A dependency's body a macro needs: asked for, and checked at the end of this
            // round, so the macro runs on the next.
            if (isExternFn(at) || isLazyFn(at)) { self.ctNeed(a, f.name); }
            self.deferReason.clear();
            self.deferReason.pushString(format("macro `{}` waits for `{}` to be checked", nameOf(m), nameOf(f.name)));
            return false;
        }
        callees: Vec<Sym>;
        self.calleesIn(a, f.body, &callees);
        for k in 0..callees.len() {
            // A global the macro reads whose own initializer still holds a macro call
            // (`gT: Vec<long> = vec![1, 2]`, held back until `vec!` can run). Run now, the
            // evaluator would meet that call unexpanded, so the macro waits for a later round.
            if (strStartsWith(nameOf(callees.get(k)), "$unexpanded:")) {
                self.deferReason.clear();
                self.deferReason.pushString(format("macro `{}` waits for the global `{}` to be checked", nameOf(m),
                                                   strSlice(nameOf(callees.get(k)), 12, nameOf(callees.get(k)).len - 12)));
                return false;
            }
            hit: Option<long> = self.fnAt.find(nameOf(callees.get(k)));
            match hit {
                Some(i) { if (!self.bodyReady(a, i, seen, m)) { return false; } }
                None {
                    // No body by that name yet: a generic instance the driver has not stamped,
                    // or something outside the program, which the evaluator will refuse.
                    if (gReg.findRequestSym(callees.get(k)) >= 0 || self.isWanted(callees.get(k))) {
                        self.deferReason.clear();
                        self.deferReason.pushString(format("macro `{}` waits for `{}` to be stamped", nameOf(m), nameOf(callees.get(k))));
                        return false;
                    }
                }
            }
        }
        return true;
    }

    // A generic function's instance this round asked for, which the next one stamps.
    isWanted &self n:Sym -> bool {
        for k in 0..self.wanted.len() {
            if (self.wanted.get(k).instance == n) { return true; }
        }
        return false;
    }

    // The macros a block invokes, by the bare names written, and the functions a typed block
    // calls, by their resolved names. Two walks of the same shape.
    macroCallsIn &self inout a:Ast b:long inout out:Vec<Sym> -> void { self.namesIn(a, b, out, true); }
    calleesIn &self inout a:Ast b:long inout out:Vec<Sym> -> void { self.namesIn(a, b, out, false); }
    namesIn &self inout a:Ast b:long inout out:Vec<Sym> macros:bool -> void {
        if (b < 0) { return; }
        n: long = a.blockLen(b);
        for k in 0..n { self.namesInStmt(a, a.stmtAt(b, k), out, macros); }
    }
    namesInStmt &self inout a:Ast st:Stmt inout out:Vec<Sym> macros:bool -> void {
        if (st.kind == StmtKind.VarDecl) { self.namesInExpr(a, a.decls.get(st.at).init, out, macros); return; }
        if (st.kind == StmtKind.Expr || st.kind == StmtKind.Call) { self.namesInExpr(a, a.exprStmts.get(st.at).value, out, macros); return; }
        if (st.kind == StmtKind.Return) { self.namesInExpr(a, a.returns.get(st.at).value, out, macros); return; }
        if (st.kind == StmtKind.If) {
            at: long = st.at;
            while (at >= 0) {
                br: IfNode = a.ifs.get(at);
                self.namesInExpr(a, br.cond, out, macros);
                self.namesIn(a, br.body, out, macros);
                at = br.elseIf;
            }
            return;
        }
        if (st.kind == StmtKind.While || st.kind == StmtKind.Recover) {
            w: WhileNode = a.whiles.get(st.at);
            self.namesInExpr(a, w.cond, out, macros); self.namesIn(a, w.body, out, macros); self.namesIn(a, w.step, out, macros);
            return;
        }
        if (st.kind == StmtKind.Loop || st.kind == StmtKind.Block || st.kind == StmtKind.Unsafe) {
            self.namesIn(a, a.blockStmts.get(st.at).body, out, macros);
            return;
        }
        if (st.kind == StmtKind.Match) {
            m: MatchNode = a.matches.get(st.at);
            for k in 0..m.armCount { self.namesIn(a, a.arms.get(m.firstArm + k).body, out, macros); }
            return;
        }
        if (st.kind == StmtKind.With) { self.namesIn(a, a.withs.get(st.at).body, out, macros); return; }
        if (st.kind == StmtKind.Destructure) { self.namesInExpr(a, a.destructures.get(st.at).value, out, macros); return; }
        if (st.kind == StmtKind.Asm) {
            n: AsmNode = a.asms.get(st.at);
            for k in 0..n.pieceCount {
                pc: AsmPiece = a.asmPieces.get(n.firstPiece + k);
                if (pc.kind == AsmKind.In) { self.namesInExpr(a, pc.value, out, macros); }
            }
        }
    }
    namesInExpr &self inout a:Ast id:NodeId inout out:Vec<Sym> macros:bool -> void {
        if (id == NO_NODE) { return; }
        e: Expr = a.expr(id);
        if (e.left != NO_NODE) { self.namesInExpr(a, e.left, out, macros); self.namesInExpr(a, e.right, out, macros); return; }
        // A global a macro reads is initialized on that read, by its own initializer, so that
        // initializer's callees are the macro's callees too.
        if (e.op == Op.Lvalue && !macros) {
            match e.payload {
                Name(n) {
                    gi: long = gReg.findGlobalSym(n);
                    if (gi >= 0) {
                        g: GlobalDef = gReg.globalDef(gi);
                        if (g.init != NO_NODE && a.expr(g.init).op != Op.Literal && !self.initSeen.has(nameOf(n))) {
                            self.initSeen.put(nameOf(n), true);
                            mc: Vec<Sym>;
                            self.namesInExpr(a, g.init, &mc, true);
                            if (mc.len() > 0) { out.push(internString(format("$unexpanded:{}", nameOf(n)))); }
                            self.namesInExpr(a, g.init, out, macros);
                        }
                    }
                }
                _ { }
            }
            return;
        }
        if (e.op == Op.MacroCall || e.op == Op.FunctionCall || e.op == Op.MethodCall) {
            c: CallNode = a.calls.get(0);
            match e.payload { Call(i) { c = a.calls.get(i); } _ { } }
            if ((e.op == Op.MacroCall) == macros && c.slot == NO_SLOT && c.callee == NO_NODE) { out.push(c.name); }
            if (c.receiver != NO_NODE) { self.namesInExpr(a, c.receiver, out, macros); }
            for k in 0..c.argCount { self.namesInExpr(a, a.argAt(c, k), out, macros); }
            return;
        }
        match e.payload {
            Sub(v)   { self.namesInExpr(a, v, out, macros); }
            Field(i) { self.namesInExpr(a, a.fields.get(i).base, out, macros); }
            Index(i) {
                ix: IndexNode = a.indexes.get(i);
                self.namesInExpr(a, ix.base, out, macros); self.namesInExpr(a, ix.index, out, macros);
                self.namesInExpr(a, ix.sliceStart, out, macros); self.namesInExpr(a, ix.sliceEnd, out, macros);
            }
            Lit(i) {
                l: LitNode = a.lits.get(i);
                for k in 0..l.initCount { self.namesInExpr(a, a.inits.get(l.firstInit + k).value, out, macros); }
                self.namesInExpr(a, l.rest, out, macros);
            }
            _ { }
        }
    }

    // ─── expansion ───────────────────────────────────────────────────────────

    // Run the macro a call names, on its arguments. Answers the result; `mi` is the macro.
    runMacroCall &self inout a:Ast id:NodeId -> CtValue {
        e: Expr = a.expr(id);
        c: CallNode = a.calls.get(0);
        match e.payload { Call(i) { c = a.calls.get(i); } _ { } }
        q: Sym = self.resolveFn(c.name);
        hit: Option<long> = self.fnAt.find(nameOf(q));
        mi: long = -1;
        match hit { Some(i) { mi = i; } None { } }
        if (mi < 0 || !gReg.isMacro(q)) { failStr(format("cannot find macro `{}!` in this scope", nameOf(c.name))); }
        f: FnNode = a.fns.get(mi);
        if (!self.macroRunnable(a, c.name)) {
            failStr(format("macro `{}` is used before it can run\nhelp: declare it, and what it calls, ahead of this use", nameOf(c.name)));
        }
        if (f.argCount != c.argCount) {
            failStr(format("wrong number of arguments to macro `{}`: expected {}, found {}", nameOf(c.name), f.argCount, c.argCount));
        }
        nodeSym: Sym = intern("ast::Node");
        self.ev.nodeSym = nodeSym;
        self.ev.macroFile = NO_SYM;
        self.ev.macroPkg = NO_SYM;
        if (self.curFn >= 0) {
            cf: FnNode = a.fns.get(self.curFn);
            self.ev.macroFile = cf.file;
            self.ev.macroPkg = cf.pkg;
        } else if (self.curStmt >= 0) {
            st: Stmt = a.stmts.get(self.curStmt);
            if (st.kind == StmtKind.VarDecl) {
                gi: long = gReg.findGlobalSym(a.decls.get(st.at).name);
                if (gi >= 0) { self.ev.macroFile = gReg.globalDef(gi).file; self.ev.macroPkg = gReg.globalDef(gi).pkg; }
            }
        }
        self.ev.beginMacro(a, self.page);
        vals: Vec<CtValue>;
        for k in 0..c.argCount {
            p: VarDeclNode = a.paramAt(f, k);
            arg: NodeId = a.argAt(c, k);
            if (p.kind == Lit.Struct && p.structName == nodeSym) {
                // The tree, not the value: quoted, then typed and built like any quote.
                qt: Quoter = Quoter { node: nodeSym, binOp: intern("ast::BinOp"), unOp: intern("ast::UnOp") };
                built: NodeId = qt.quoteTree(a, arg);
                self.checkExpr(a, built);
                v: CtValue = self.ev.evalExpr(a, self.page, built);
                if (self.ev.stopped) { failStr(format("macro `{}` cannot build the tree for its parameter `{}`: it met {}", nameOf(c.name), nameOf(p.name), self.ev.refusal)); }
                vals.push(v);
            } else {
                self.checkExpr(a, arg);
                v: CtValue = self.ev.evalExpr(a, self.page, arg);
                if (self.ev.stopped) { failStr(format("macro `{}` needs a value the compiler can compute for `{}`: it met {}", nameOf(c.name), nameOf(p.name), self.ev.refusal)); }
                vals.push(v);
            }
        }
        r: CtValue = self.ev.runMacro(a, self.page, mi, vals);
        // Ended by its own decision (an `exit`, a `refuse`): what it wrote is the error.
        if (self.ev.stopped && self.ev.refused) { failStr(format("macro `{}` stopped: {}", nameOf(c.name), self.ev.refusal)); }
        if (self.ev.stopped) { failStr(format("macro `{}` could not run: it met {}", nameOf(c.name), self.ev.refusal)); }
        return r;
    }
    macroReturnsNode &self inout a:Ast id:NodeId -> bool {
        e: Expr = a.expr(id);
        c: CallNode = a.calls.get(0);
        match e.payload { Call(i) { c = a.calls.get(i); } _ { } }
        hit: Option<long> = self.fnAt.find(nameOf(self.resolveFn(c.name)));
        match hit {
            Some(i) { f: FnNode = a.fns.get(i); return f.returnKind == Lit.Struct && f.returnStruct == intern("ast::Node"); }
            None { }
        }
        return false;
    }
    macroName &self inout a:Ast id:NodeId -> Sym {
        e: Expr = a.expr(id);
        match e.payload { Call(i) { return a.calls.get(i).name; } _ { } }
        return NO_SYM;
    }

    // In expression position: a Node result is the expression it describes, a scalar result a
    // literal. Either replaces the call in place and is checked where it landed.
    expandMacroExpr &self inout a:Ast id:NodeId -> VarType {
        self.spliceMacroCall(a, id);
        return self.checkExpr(a, id);
    }
    // Run the macro and put what it returned in the call's place, not yet checked, so the
    // caller may aim it at a destination first.
    spliceMacroCall &self inout a:Ast id:NodeId -> void {
        // An error while a macro runs leaves the evaluator mid-run: no going on past it.
        gNoResume = gNoResume + 1;
        r: CtValue = self.runMacroCall(a, id);
        if (self.macroReturnsNode(a, id)) {
            self.ev.renames.clear();
            self.ev.macroSeq = self.ev.macroSeq + 1;
            root: NodeId = self.ev.spliceExpr(a, r.bits);
            a.setExpr(id, a.expr(root));
            gNoResume = gNoResume - 1;
            return;
        }
        gNoResume = gNoResume - 1;
        if (ctScalar(r.kind, r.structName)) {
            a.setExpr(id, Expr { op: Op.Literal, left: NO_NODE, right: NO_NODE, kind: r.kind,
                                 structName: r.structName, isParen: false, payload: Payload.Num(r.bits) });
            return;
        }
        failStr(format("macro `{}` returns a value of type `{}`\nnote: a macro returns a `Node`, or a number", nameOf(self.macroName(a, id)), typeName(r.kind)));
    }

    // In statement position: a Node result is the statement(s) it describes, replacing the
    // statement; anything else is discarded.
    expandMacroStmt &self inout a:Ast stmtId:long -> void {
        st: Stmt = a.stmts.get(stmtId);
        id: NodeId = a.exprStmts.get(st.at).value;
        gNoResume = gNoResume + 1;
        r: CtValue = self.runMacroCall(a, id);
        if (self.macroReturnsNode(a, id)) {
            self.ev.renames.clear();
            self.ev.macroSeq = self.ev.macroSeq + 1;
            produced: long = self.ev.spliceStmt(a, r.bits);
            a.stmts.set(stmtId, a.stmts.get(produced));
            gNoResume = gNoResume - 1;
            return;
        }
        gNoResume = gNoResume - 1;
        ids: Vec<long>;
        a.blockStmts.push(BlockStmtNode { body: a.addBlock(ids) });
        a.stmts.set(stmtId, Stmt { kind: StmtKind.Block, at: a.blockStmts.len() - 1 });
    }
}

// ─── upstream bodies compile-time code reaches ───────────────────────────────
//
// In a package build a dependency's functions arrive unchecked: their package checked them, and
// the facts table carries what that decided. The evaluator is the one consumer that needs a body
// rather than a fact, so whatever it can run here (a macro, a global's initializer, and
// everything those call) is found by walking the typed bodies from those roots, and each
// dependency function on the way is checked on demand. Generous rather than exact: a dispatch
// reaches every implementation, and every type a reached body handles is assumed dropped, since
// the ownership pass has not yet written the drops in.

methods Checker {
    // `n` is reached by compile-time code.
    ctNeed &self inout a:Ast n:Sym -> void {
        if (n == NO_SYM) { return; }
        key: str = nameOf(n);
        // Reached by code that runs: only a lazy method needs anything done (it is checked, and
        // so compiled). A dependency's function is linked, not compiled.
        if (self.walkRuntime) {
            if (self.rtSeen.has(key)) { return; }
            self.rtSeen.put(key, true);
            rt: long = self.fnNodeOf(n);
            if (rt >= 0 && isLazyFn(rt) && !isExternReady(rt)) { self.demandQ.push(rt); }
            return;
        }
        if (self.ctSeen.has(key)) { return; }
        self.ctSeen.put(key, true);
        at: long = self.fnNodeOf(n);
        // Not on the page yet: a generic instance the next round stamps. `ctSeen` remembers it,
        // and checking it walks it.
        if (at < 0) { return; }
        if (isLazyFn(at)) {
            if (!isExternReady(at)) { self.demandQ.push(at); }
            else if (self.fnDone.has(key)) { self.ctWork.push(at); }
            return;
        }
        if (isExternFn(at)) {
            if (isExternReady(at)) { return; }
            // The types its module's bodies name were held back, since nothing here checked
            // them. Released now; if that leaves instances to stamp, the body waits a round for
            // them, the way a function waits for a macro.
            if (gReg.releaseModule(a.fns.get(at).file)) {
                hit: Option<long> = self.stmtOfFn.find(key);
                match hit { Some(sid) { self.deferredFns.push(sid); } None { } }
                self.deferReason.clear();
                self.deferReason.pushString(format("`{}` waits for the types its module names to be stamped", key));
                return;
            }
            self.demandQ.push(at);
            return;
        }
        if (self.fnDone.has(key)) { self.ctWork.push(at); }
    }

    // A type whose value reached code may release: its `drop`, and its fields' in turn, which
    // the glue the ownership pass writes later will call.
    ctNeedDrop &self inout a:Ast s:Sym depth:long -> void {
        if (s == NO_SYM || depth > 16 || !gReg.needsDrop(s)) { return; }
        dn: Sym = methodSymbol(s, intern("drop"));
        if (self.walkRuntime && self.rtSeen.has(nameOf(dn))) { return; }
        if (!self.walkRuntime && self.ctSeen.has(nameOf(dn))) { return; }
        self.ctNeed(a, dn);
        at: long = gReg.findStructSym(s);
        if (at < 0) { return; }
        d: StructDef = gReg.structDef(at);
        for k in 0..d.fieldCount {
            f: FieldDef = gReg.fieldAt(d, k);
            if (f.kind == Lit.Struct) { self.ctNeedDrop(a, f.structName, depth + 1); }
        }
    }

    // A checked body's runtime references: every lazy method it can reach becomes needed.
    rtWalk &self inout a:Ast b:long -> void {
        self.walkRuntime = true;
        self.ctReachBlock(a, b);
        self.walkRuntime = false;
    }
    rtWalkExpr &self inout a:Ast id:NodeId -> void {
        if (gKnownInstances.isEmpty()) { return; }
        self.walkRuntime = true;
        self.ctReachExpr(a, id);
        self.walkRuntime = false;
    }

    // Every checked body reached so far, walked; walking one reaches more.
    drainWalk &self inout a:Ast -> void {
        while (self.ctWork.len() > 0) {
            at: long = self.ctWork.pop();
            self.ctReachBlock(a, a.fns.get(at).body);
        }
    }

    // The dependency bodies asked for, checked; checking one walks it, which can ask for more.
    drainDemand &self inout a:Ast -> void {
        self.drainWalk(a);
        while (self.demandQ.len() > 0) {
            at: long = self.demandQ.pop();
            if (isExternReady(at)) { continue; }
            hit: Option<long> = self.stmtOfFn.find(nameOf(a.fns.get(at).name));
            sid: long = -1;
            match hit { Some(s) { sid = s; } None { continue; } }
            was: long = self.curStmt;
            self.curStmt = sid;
            self.checkStmtAt(a, sid);
            self.curStmt = was;
            self.drainWalk(a);
        }
    }

    ctReachBlock &self inout a:Ast b:long -> void {
        if (b < 0) { return; }
        n: long = a.blockLen(b);
        for k in 0..n { self.ctReachStmt(a, a.stmtAt(b, k)); }
    }

    ctReachStmt &self inout a:Ast st:Stmt -> void {
        if (st.kind == StmtKind.VarDecl) {
            d: VarDeclNode = a.decls.get(st.at);
            if (d.kind == Lit.Struct) {
                self.ctNeedDrop(a, d.structName, 0);
                // An array of owning values is built element by element by the ownership pass,
                // with each one's `new`.
                if (d.isArray) { self.ctNeed(a, self.resolveFn(methodSymbol(d.structName, intern("new")))); }
            }
            self.ctReachExpr(a, d.init);
            return;
        }
        if (st.kind == StmtKind.Expr || st.kind == StmtKind.Call) { self.ctReachExpr(a, a.exprStmts.get(st.at).value); return; }
        if (st.kind == StmtKind.Return) { self.ctReachExpr(a, a.returns.get(st.at).value); return; }
        if (st.kind == StmtKind.If) {
            at: long = st.at;
            while (at >= 0) {
                br: IfNode = a.ifs.get(at);
                self.ctReachExpr(a, br.cond);
                self.ctReachBlock(a, br.body);
                at = br.elseIf;
            }
            return;
        }
        if (st.kind == StmtKind.While || st.kind == StmtKind.Recover) {
            w: WhileNode = a.whiles.get(st.at);
            self.ctReachExpr(a, w.cond); self.ctReachBlock(a, w.body); self.ctReachBlock(a, w.step);
            return;
        }
        if (st.kind == StmtKind.Loop || st.kind == StmtKind.Block || st.kind == StmtKind.Unsafe) {
            self.ctReachBlock(a, a.blockStmts.get(st.at).body);
            return;
        }
        if (st.kind == StmtKind.Match) {
            m: MatchNode = a.matches.get(st.at);
            for k in 0..m.armCount {
                arm: ArmNode = a.arms.get(m.firstArm + k);
                self.ctReachExpr(a, arm.test);
                self.ctReachBlock(a, arm.body);
            }
            return;
        }
        if (st.kind == StmtKind.With) { self.ctReachBlock(a, a.withs.get(st.at).body); return; }
        if (st.kind == StmtKind.Destructure) { self.ctReachExpr(a, a.destructures.get(st.at).value); return; }
        if (st.kind == StmtKind.Asm) {
            n: AsmNode = a.asms.get(st.at);
            for k in 0..n.pieceCount {
                pc: AsmPiece = a.asmPieces.get(n.firstPiece + k);
                if (pc.kind == AsmKind.In) { self.ctReachExpr(a, pc.value); }
            }
        }
    }

    ctReachExpr &self inout a:Ast id:NodeId -> void {
        if (id == NO_NODE) { return; }
        e: Expr = a.expr(id);
        if (e.kind == Lit.Struct) { self.ctNeedDrop(a, e.structName, 0); }
        if (e.left != NO_NODE) { self.ctReachExpr(a, e.left); self.ctReachExpr(a, e.right); return; }
        if (e.op == Op.FunctionCall || e.op == Op.MethodCall) {
            c: CallNode = a.calls.get(0);
            match e.payload { Call(i) { c = a.calls.get(i); } _ { } }
            if (c.slot >= 0 && c.receiver != NO_NODE) {
                self.ctNeedDispatch(a, a.expr(c.receiver).structName, c.slot);
            } else if (c.slot == NO_SLOT && c.callee == NO_NODE) {
                self.ctNeed(a, c.name);
            }
            self.ctReachExpr(a, c.receiver);
            self.ctReachExpr(a, c.callee);
            // A value boxed into a `...any` run is shown through its `Display`, which the
            // formatter calls through the vtable it reads out of the box.
            anyFrom: long = self.anyRunStart(a, c);
            k: long = 0;
            while (k < c.argCount) {
                arg: NodeId = a.argAt(c, k);
                if (anyFrom >= 0 && k >= anyFrom) {
                    ae: Expr = a.expr(arg);
                    if ((ae.kind == Lit.Struct || ae.kind == Lit.Ref) && ae.structName != NO_SYM) {
                        self.ctNeedImpl(a, ae.structName, intern("Display"));
                    }
                    if (ae.kind == Lit.TraitObj) { self.ctNeedDispatch(a, ae.structName, 0); }
                }
                self.ctReachExpr(a, arg);
                k = k + 1;
            }
            return;
        }
        // A function's name as a value: whatever is called through it later.
        if (e.kind == Lit.Fn && (e.op == Op.Lvalue || e.op == Op.AddressOf)) {
            match e.payload {
                Name(n) { self.ctNeed(a, n); }
                Sub(v) {
                    inner: Expr = a.expr(v);
                    match inner.payload { Name(n) { self.ctNeed(a, n); } _ { } }
                }
                _ { }
            }
            return;
        }
        // A value seen as a trait object: its vtable's methods are what a dispatch reaches.
        if (e.op == Op.MakeTraitObj) {
            match e.payload {
                Sub(v) {
                    self.ctNeedImpl(a, a.expr(v).structName, e.structName);
                    self.ctReachExpr(a, v);
                }
                _ { }
            }
            return;
        }
        match e.payload {
            Sub(v)   { self.ctReachExpr(a, v); }
            Field(i) { self.ctReachExpr(a, a.fields.get(i).base); }
            Index(i) {
                ix: IndexNode = a.indexes.get(i);
                self.ctReachExpr(a, ix.base); self.ctReachExpr(a, ix.index);
                self.ctReachExpr(a, ix.sliceStart); self.ctReachExpr(a, ix.sliceEnd);
            }
            Lit(i) {
                l: LitNode = a.lits.get(i);
                for at in 0..l.initCount { self.ctReachExpr(a, a.inits.get(l.firstInit + at).value); }
                self.ctReachExpr(a, l.rest);
            }
            _ { }
        }
    }

    // Which of a call's arguments land in its callee's `...any` run, as an argument index; -1
    // when the callee has none (or is not a function the program holds by name).
    anyRunStart &self inout a:Ast c:CallNode -> long {
        if (c.slot != NO_SLOT || c.callee != NO_NODE) { return -1; }
        at: long = self.fnNodeOf(c.name);
        if (at < 0) { return -1; }
        f: FnNode = a.fns.get(at);
        if (f.argCount == 0) { return -1; }
        last: VarDeclNode = a.paramAt(f, f.argCount - 1);
        if (!last.isVariadic || last.elemKind != Lit.Any) { return -1; }
        base: long = 0;
        if (c.receiver != NO_NODE) { base = 1; }
        return f.argCount - 1 - base;
    }

    // The methods of `concrete`'s implementation of the trait `mangled` names.
    ctNeedImpl &self inout a:Ast concrete:Sym mangled:Sym -> void {
        if (concrete == NO_SYM || mangled == NO_SYM) { return; }
        ii: long = gReg.findImplMangled(concrete, mangled);
        if (ii < 0) { return; }
        im: TraitImplDef = gReg.implAt(ii);
        for k in 0..im.fnCount { self.ctNeed(a, gReg.implFnAt(im, k)); }
    }

    // A dispatch through a trait object reaches whichever implementation it holds: all of them.
    ctNeedDispatch &self inout a:Ast mangled:Sym slot:long -> void {
        if (mangled == NO_SYM) { return; }
        for i in 0..gReg.implCount() {
            im: TraitImplDef = gReg.implAt(i);
            if (gReg.traitMangled(im.trait) == nameOf(mangled) && slot < im.fnCount) {
                self.ctNeed(a, gReg.implFnAt(im, slot));
            }
        }
    }
}

// ─── derives: `trait T derive m` ─────────────────────────────────────────────
//
// A trait may name a macro that writes its implementation for a type that has none:
// `trait Encode derive deriveEncode { ... }`. Nothing here knows any particular trait. When the
// walk needs `X: T` (a method of T called on an X, a static one called on the type, an X made
// into a T object) and X has no implementation, one is found in this order:
//
//   1. a hand-written `methods X for T` (already registered: it always wins);
//   2. X is an instance of a generic type whose template implements T under bounds X's
//      arguments did not meet when X was stamped (`methods Vec<T: Encode> for Encode` and a
//      `Vec<Point>` named before `Point: Encode` existed): the bounds are met now, each by these
//      same rules, and the implementation is stamped for X (`lateImpl`);
//   3. T's derive: the implementation is STUBBED at once, its functions declared with T's
//      signatures (`Self` being X), so the call that asked is typed against the real thing, and
//      the macro writes the bodies at the end of the round, once it can run (`runDerives`).
//
// The macro is handed X's declaration as a `stdlib::reflect` value and returns a `MethodsDecl`
// Node (`quote { methods @(t.name) for Encode { ... } }`), which is held to T's signatures,
// put where the stubs stood, and checked like hand-written code; checking it may need more. A
// macro that calls `refuse(why)` stops the compile with `why`, naming X, T, and the function
// that needed it. The macro sees the INSTANCE of a generic type (`Pair_long_String`, fields at
// their concrete types), which is what its code has to be written for.

methods Checker {
    // What is left for the derive machinery: stubs waiting for their macro, and stamped methods
    // waiting for their types to be laid out.
    deriveWork &self -> long { return self.deriveQ.len() + self.lateFns.len(); }
    takeLate &self -> Vec<long> {
        out: Vec<long>;
        out.extend(self.lateFns);
        self.lateFns.clear();
        return out;
    }

    // `x.m(...)` (or `T.m(...)` on the type, when `isStatic`) found no `m`: is there a trait
    // declaring it that `owner` can be given? True once `owner_m` is registered.
    implementForMethod &self inout a:Ast owner:Sym m:Sym isStatic:bool -> bool {
        if (!gReg.hasDerives() || owner == NO_SYM) { return false; }
        for i in 0..gReg.traits.len() {
            t: TraitDef = gReg.traitDef(i);
            if (t.paramCount > 0) { continue; }
            slot: long = gReg.methodSlot(t, nameOf(m));
            if (slot < 0 || gReg.traitMethodAt(t, slot).isStatic != isStatic) { continue; }
            if (self.ensureImpl(a, owner, t.name, 0)) {
                return self.fnNames.has(nameOf(implFnName(owner, TraitRef { name: t.name, firstArg: 0, argCount: 0 }, m)));
            }
        }
        return false;
    }

    // Does `owner` implement `tr`, or can it be made to (see above)?
    ensureImpl &self inout a:Ast owner:Sym tr:Sym depth:long -> bool {
        if (owner == NO_SYM || tr == NO_SYM || depth > 32) { return false; }
        if (gReg.structImplements(nameOf(owner), tr)) { return true; }
        late: long = self.lateImpl(a, owner, tr, depth);
        if (late == 1) { return true; }
        if (late == 2) { return false; }          // the template's own implementation, unmet
        if (gReg.deriveMacroOf(tr) == NO_SYM) { return false; }
        // Something with a declaration to hand the macro: a struct, a sum type, or an enum of
        // named integers. A scalar has none.
        if (gReg.findStructSym(owner) < 0 && gReg.findEnumSym(owner) < 0) { return false; }
        if (isClosureCall(owner)) { return false; }
        self.stubDerive(a, owner, tr);
        return true;
    }

    // 0: `owner` is not an instance of a template implementing `tr`; 1: it is, and that
    // implementation is stamped for it now; 2: it is, and one of the block's bounds cannot be met.
    lateImpl &self inout a:Ast owner:Sym tr:Sym depth:long -> long {
        ri: long = gReg.findRequestSym(owner);
        if (ri < 0) { return 0; }
        r: GRequest = gReg.requestAt(ri);
        if (gReg.isPatternRequest(r) || r.instance != owner) { return 0; }
        found: long = -1;
        i: long = 0;
        while (i < gReg.implCount() && found < 0) {
            im: TraitImplDef = gReg.implAt(i);
            if (im.structName == r.base && im.trait.name == tr && im.trait.argCount == 0) { found = i; }
            i = i + 1;
        }
        if (found < 0) { return 0; }
        im: TraitImplDef = gReg.implAt(found);
        ti: long = gReg.findTraitSym(tr);
        if (ti < 0) { return 0; }
        td: TraitDef = gReg.traitDef(ti);
        args: Vec<TypeRef>;
        for k in 0..r.argCount { args.push(gReg.gArgAt(r, k)); }
        // Every method's bounds (they are the block's, carried by each), each met by these rules.
        have: Vec<bool>;
        for k in 0..td.methodCount {
            m: Sym = gReg.traitMethodAt(td, k).name;
            have.push(self.fnNames.has(nameOf(implFnNameAs(owner, im.trait, m, im.carried))));
            at: long = self.late.fnDefOf(a, implMethodName(im, m));
            if (at >= 0) {
                f: FnNode = a.fns.get(at);
                for b in 0..f.boundCount {
                    mb: MethodBound = gReg.boundAt(f.firstBound + b);
                    if (mb.param >= args.len()) { continue; }
                    if (!self.meetsBound(a, args.get(mb.param), mb.trait.name, depth)) { return 2; }
                }
            }
        }
        before: long = gReg.requestCount();
        gNoResume = gNoResume + 1;          // stamping: no going on past an error in it
        ids: Vec<long> = self.late.stampImpl(a, r.base, owner, args, im, have);
        gNoResume = gNoResume - 1;
        // A body naming an instance nobody had asked for waits a round for it to be laid out.
        laidOut: bool = gReg.requestCount() == before;
        for k in 0..ids.len() {
            id: long = ids.get(k);
            f: FnNode = a.fns.get(a.stmts.get(id).at);
            self.fnAt.put(nameOf(f.name), a.stmts.get(id).at);
            self.stmtOfFn.put(nameOf(f.name), id);
            self.noteReturn(f.name, varType(f.returnKind, f.returnStruct));
            self.eqExtra.push(id);
            if (laidOut) { self.lateNow.push(id); } else { self.lateFns.push(id); }
        }
        return 1;
    }
    meetsBound &self inout a:Ast t:TypeRef tr:Sym depth:long -> bool {
        if (self.late.satisfies(t, tr)) { return true; }
        if (t.base != Lit.Struct) { return false; }
        return self.ensureImpl(a, t.name, tr, depth + 1);
    }

    // `owner`'s implementation of `tr`, declared now with the trait's signatures (the receiver
    // as the trait takes it, `Self` as `owner`) and registered, its bodies left to the macro.
    // The stubs are not on the page until the macro has written them.
    stubDerive &self inout a:Ast owner:Sym tr:Sym -> void {
        td: TraitDef = gReg.traitDef(gReg.findTraitSym(tr));
        fns: Vec<Sym>;
        carried: bool = gReg.flatCarries(owner, TraitRef { name: tr, firstArg: 0, argCount: 0 });
        for k in 0..td.methodCount {
            sig: TraitMethodSig = gReg.traitMethodAt(td, k);
            name: Sym = implFnNameAs(owner, TraitRef { name: tr, firstArg: 0, argCount: 0 }, sig.name, carried);
            fns.push(name);
            params: Vec<long>;
            if (!sig.isStatic) {
                rt0: TypeRef = selfAs(Lit.Struct, intern("Self"), owner);
                rc: Conv = Conv.Sink;
                if (sig.lentSelf) { rt0 = selfAs(Lit.Ref, intern("Self"), owner); rc = Conv.Inout; }
                a.decls.push(VarDeclNode { name: intern("self"), kind: rt0.base, structName: rt0.name, isArray: false,
                                           count: 0, conv: rc, isVariadic: false, elemKind: Lit.Void,
                                           elemStruct: NO_SYM, init: NO_NODE });
                params.push(a.decls.len() - 1);
            }
            for i in 0..sig.paramCount {
                p: VarDeclNode = a.decls.get(a.params.get(sig.firstParam + i));
                t: TypeRef = selfAs(p.kind, p.structName, owner);
                a.decls.push(VarDeclNode { name: p.name, kind: t.base, structName: t.name, isArray: p.isArray,
                                           count: p.count, conv: p.conv, isVariadic: p.isVariadic,
                                           elemKind: p.elemKind, elemStruct: p.elemStruct, init: NO_NODE });
                params.push(a.decls.len() - 1);
            }
            rt: TypeRef = selfAs(sig.returnKind, sig.returnName, owner);
            firstArg: long = a.addParams(params);
            a.fns.push(FnNode { name: name, returnKind: rt.base, returnStruct: rt.name, visibility: Vis.Pub,
                                file: NO_SYM, pkg: NO_SYM, isUnsafe: false, isTemplate: false, inferReturn: false,
                                firstBound: 0, boundCount: 0, firstArg: firstArg, argCount: params.len(),
                                body: -1 });
            self.fnAt.put(nameOf(name), a.fns.len() - 1);
            self.noteReturn(name, varType(rt.base, rt.name));
        }
        gReg.addImplAs(owner, TraitRef { name: tr, firstArg: 0, argCount: 0 }, fns, carried);
        req: Sym = NO_SYM;
        if (self.curFn >= 0) { req = a.fns.get(self.curFn).name; }
        self.deriveQ.push(DeriveJob { owner: owner, trait: tr, requester: req, pos: gPos });
    }

    // End of a round: every stub whose macro can run is written and checked, which may stub
    // more, and every stamped method whose types are laid out is checked; until neither moves.
    runDerives &self inout a:Ast -> void {
        going: bool = true;
        while (going) {
            going = false;
            while (self.lateNow.len() > 0) { self.checkMadeStmt(a, self.lateNow.pop()); going = true; }
            i: long = 0;
            while (i < self.deriveQ.len()) {
                job: DeriveJob = self.deriveQ.get(i);
                mi: long = self.deriveMacroAt(a, job.trait);
                seen: HashMap<str, bool>;
                self.initSeen.clear();
                if (!self.bodyReady(a, mi, &seen, a.fns.get(mi).name)) { i = i + 1; continue; }
                self.deriveQ.removeAt(i);
                was: long = gPos;
                gPos = job.pos;
                self.runDerive(a, job, mi);
                gPos = was;
                self.derivesRun = self.derivesRun + 1;
                going = true;
            }
            // A dependency's body a macro waits for is checked here (`bodyReady` asked for it), after
            // which the macro may be able to run.
            checked: long = self.fnDone.len();
            self.drainDemand(a);
            if (self.fnDone.len() > checked) { going = true; }
        }
    }
    checkMadeStmt &self inout a:Ast id:long -> void {
        was: long = self.curStmt;
        self.curStmt = id;
        self.checkStmtAt(a, id);
        self.curStmt = was;
    }

    // The macro a trait derives with: its name resolved in the trait's own module.
    deriveMacroAt &self inout a:Ast tr:Sym -> long {
        bare: Sym = gReg.deriveMacroOf(tr);
        wasMod: Sym = self.currentModule;
        self.currentModule = intern(stemOf(nameOf(gReg.deriveFileOf(tr))));
        q: Sym = self.resolveFn(bare);
        self.currentModule = wasMod;
        at: long = self.fnNodeOf(q);
        if (at < 0 || !gReg.isMacro(q)) {
            failStr(format("trait `{}` derives with `{}`, which names no macro", nameOf(tr), nameOf(bare)));
        }
        return at;
    }

    // Run `job`'s macro on its type's declaration and put what it wrote where the stubs stand.
    runDerive &self inout a:Ast job:DeriveJob mi:long -> void {
        f: FnNode = a.fns.get(mi);
        tn: str = nameOf(job.trait);
        mn: str = lastComponentOf(nameOf(f.name));
        on: str = nameOf(job.owner);
        isEnum: bool = gReg.findEnum(on) >= 0;
        nodeSym: Sym = intern("ast::Node");
        view: str = "";
        if (f.argCount == 1) { view = lastComponentOf(nameOf(a.paramAt(f, 0).structName)); }
        if (view != "Struct" && view != "Enum" && view != "Decl") {
            failStr(format("derive macro `{}` for `{}` must take one parameter, the type's declaration\nnote: the parameter is a `reflect::Struct`, `reflect::Enum` or `reflect::Decl`", mn, tn));
        }
        if (f.returnKind != Lit.Struct || f.returnStruct != nodeSym) {
            failStr(format("derive macro `{}` for `{}` must return a `Node`\nnote: a derive macro returns the `Node` of a methods block", mn, tn));
        }
        if (view == "Struct" && isEnum) {
            failStr(format("`{}` does not implement `{}`\nnote: `{}` derives it for a struct only, and `{}` is an enum{}", on, tn, mn, on, self.neededBy(job)));
        }
        if (view == "Enum" && !isEnum) {
            failStr(format("`{}` does not implement `{}`\nnote: `{}` derives it for an enum only, and `{}` is a struct{}", on, tn, mn, on, self.neededBy(job)));
        }
        p: VarDeclNode = a.paramAt(f, 0);
        self.ev.nodeSym = nodeSym;
        self.ev.macroFile = f.file;
        self.ev.macroPkg = f.pkg;
        self.ev.beginMacro(a, self.page);
        vals: Vec<CtValue>;
        vals.push(CtValue { kind: p.kind, structName: p.structName, bits: self.ev.reflectView(job.owner, p.structName) });
        r: CtValue = self.ev.runMacro(a, self.page, mi, vals);
        if (self.ev.stopped) {
            if (self.ev.refused) {
                failStr(format("`{}` does not implement `{}`, and `{}` refused to derive it: {}{}", on, tn, mn, self.ev.refusal, self.neededBy(job)));
            }
            failStr(format("`{}` does not implement `{}`, and `{}` could not derive it: it met {}{}", on, tn, mn, self.ev.refusal, self.neededBy(job)));
        }
        addr: long = r.bits;
        got: str = self.ev.nodeVariant(addr);
        if (got != "MethodsDecl") {
            failStr(format("derive macro `{}` returned a node of kind `{}` for the `{}` of `{}`\nnote: a derive returns a methods block (a quote of `methods T for {}`)", mn, got, tn, on, tn));
        }
        hdr: str = nameOf(self.ev.declOwner(addr));
        if (hdr != "Self" && hdr != on) {
            failStr(format("derive macro `{}` was asked for the `{}` of `{}`, and wrote methods for `{}`", mn, tn, on, hdr));
        }
        if (lastComponentOf(nameOf(self.ev.declTrait(addr))) != lastComponentOf(tn)) {
            failStr(format("derive macro `{}` was asked for the `{}` of `{}`, and wrote methods for trait `{}`", mn, tn, on, nameOf(self.ev.declTrait(addr))));
        }
        self.ev.renames.clear();
        self.ev.macroSeq = self.ev.macroSeq + 1;
        td: TraitDef = gReg.traitDef(gReg.findTrait(tn));
        done: Vec<bool>;
        for k in 0..td.methodCount { done.push(false); }
        fns: Vec<long> = self.ev.declFns(addr);
        made: Vec<long>;
        for k in 0..fns.len() {
            name: Sym = self.ev.fnDeclName(fns.get(k));
            slot: long = gReg.methodSlot(td, nameOf(name));
            if (slot < 0) { failStr(format("derive macro `{}` wrote `{}` for `{}`, and `{}` declares no such method", mn, nameOf(name), on, tn)); }
            if (done.get(slot)) { failStr(format("derive macro `{}` wrote `{}` for `{}` twice", mn, nameOf(name), on)); }
            done.set(slot, true);
            full: Sym = implFnName(job.owner, TraitRef { name: job.trait, firstArg: 0, argCount: 0 }, name);
            // Whose code it is, for an error inside it: the derive, needed where `job.pos` stands.
            lbl: Sym = internString(format("{} for {}, derived by {}", lastComponentOf(tn), on, mn));
            noteOrigin(lbl, job.pos, lbl);
            noteFnOwner(full, lbl);
            at: long = self.fnNodeOf(full);
            fn: FnNode = self.ev.spliceFnDecl(a, fns.get(k), job.owner, full, f.file, f.pkg);
            self.requireStubShape(a, a.fns.get(at), fn, mn, tn);
            a.fns.set(at, fn);
            sid: long = a.addStmt(StmtKind.FunctionDef, at);
            self.stmtOfFn.put(nameOf(full), sid);
            self.eqExtra.push(sid);
            made.push(sid);
        }
        for k in 0..td.methodCount {
            if (!done.get(k)) {
                failStr(format("derive macro `{}` wrote no `{}` for `{}`, and `{}` declares it", mn, nameOf(gReg.traitMethodAt(td, k).name), on, tn));
            }
        }
        for k in 0..made.len() { self.checkMadeStmt(a, made.get(k)); }
    }

    // A written method against the stub its callers were typed by: the trait's signature.
    requireStubShape &self inout a:Ast want:FnNode got:FnNode mn:str tn:str -> void {
        same: bool = want.argCount == got.argCount && want.returnKind == got.returnKind
                     && want.returnStruct == got.returnStruct;
        k: long = 0;
        while (same && k < want.argCount) {
            p: VarDeclNode = a.paramAt(want, k);
            q: VarDeclNode = a.paramAt(got, k);
            if (p.kind != q.kind || p.structName != q.structName) { same = false; }
            k = k + 1;
        }
        if (!same) {
            failStr(format("derive macro `{}` wrote `{}` with a signature other than the one `{}` declares", mn, nameOf(want.name), tn));
        }
    }

    // Which function needed the derive, as a `note:` line for the end of the message, or "".
    neededBy &self job:DeriveJob -> String {
        if (job.requester == NO_SYM) { return stringOf(""); }
        return format("\nnote: needed by `{}`", nameOf(job.requester));
    }
}

// `Self` in a trait's signature, as the type it is being implemented for. A backed enum is its
// named type like any other: `methods Color for Encode` lends its `self` the same way.
local selfAs k:Lit n:Sym owner:Sym -> TypeRef {
    if (n != NO_SYM && nameOf(n) == "Self") {
        if (k == Lit.Ref) { return TypeRef { base: Lit.Ref, name: owner }; }
        return TypeRef { base: Lit.Struct, name: owner };
    }
    return TypeRef { base: k, name: n };
}

// A copy of a place made of names and fields (`placeIsArray` admits nothing else), so each store
// of a written-out array literal has its own nodes to be typed.
local clonePlace inout a:Ast id:NodeId -> NodeId {
    e: Expr = a.expr(id);
    match e.payload {
        Field(f) {
            fd: FieldNode = a.fields.get(f);
            base: NodeId = clonePlace(a, fd.base);
            a.fields.push(FieldNode { base: base, name: fd.name });
            return a.leafOf(e.op, Payload.Field(a.fields.len() - 1), e.kind, e.structName);
        }
        _ { }
    }
    return a.leafOf(e.op, e.payload, e.kind, e.structName);
}
