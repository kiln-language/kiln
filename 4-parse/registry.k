// What has been declared.
//
// One table per kind of declaration, each keyed by a qualified name (`module::Name`), since a name
// belongs to the module that declares it and two modules may use the same one. The parser writes
// these as it goes and every later phase only reads them.
#include <{ast, types}>
#include <support::{compiler, imports}>
#include <stdlib::{chars, encode, map, option, string, vec}>

pub NOT_FOUND: long = -1;

// What a bare name resolved to, and (when the answer was not unique) the other module that
// also declares it. Two modules may each declare a name; only a file that can reach both is
// ambiguous, and it has to be told so rather than handed whichever registered first.
pub struct BareName { name: Sym, rival: Sym }

// The one wording for that, so the parser (which can point at the line) and a caller with no
// position to give both say the same thing.
pub ambiguousName bare:str b:BareName -> String {
    return format("`{}` is ambiguous\nnote: it could refer to `{}` or to `{}`\nhelp: write which one you mean, as `{}`",
                  bare, nameOf(b.name), nameOf(b.rival), nameOf(b.rival));
}

// `module::Name` from its two halves, the spelling every table here is keyed by.
pub qualifiedName mod:str bare:str -> Sym {
    s: String;
    s.pushStr(mod);
    s.pushStr("::");
    s.pushStr(bare);
    return internString(s);
}

// `qualifiedName` of two symbols, with each pair worked out only once. The checker asks this for
// every name it resolves, and building and interning the text every time was a noticeable share
// of the compile on its own.
local var gQualMemo: HashMap<long, long> = map![];
pub qualifiedSym mod:Sym bare:Sym -> Sym {
    if ((mod as long) < 0 || (bare as long) < 0) { return qualifiedName(nameOf(mod), nameOf(bare)); }
    key: long = ((mod as long) << 32) | (bare as long);
    hit: Option<long> = gQualMemo.find(key);
    match hit { Some(q) { return q as Sym; } None { } }
    q: Sym = qualifiedName(nameOf(mod), nameOf(bare));
    gQualMemo.put(key, q as long);
    return q;
}

// The module a qualified name was declared in: everything before the last `::`. NO_SYM when the
// name carries no module, which is what a runtime hook and a trait's flat name look like.
pub moduleOfName q:str -> Sym {
    i: long = 0;
    cut: long = -1;
    while (i + 1 < q.len) {
        if (charAt(q, i) == ':' && charAt(q, i + 1) == ':') { cut = i; }
        i = i + 1;
    }
    if (cut < 0) { return NO_SYM; }
    return intern(strSlice(q, 0, cut));
}

// Every qualified declaration of one bare name, as a chain through flat arrays.
//
// Resolving `opName` by building `<module>::opName` for every module the caller can see, and
// asking whether each was declared, costs O(visible modules) per name and makes a program's build
// quadratic in its module count. This index answers the inverse question: it gives the
// declarations of `opName` directly (almost always just one), and the import graph then says
// whether that one is visible.
//
// It is a chain rather than a run because declarations arrive while the program is still being
// parsed, and a run cannot be appended to once the next one has started.
pub struct BareIndex {
    head: HashMap<str, long>,
    qual: Vec<Sym>,
    owner: Vec<Sym>,
    next: Vec<long>
}

methods BareIndex for Default {
    new -> BareIndex { return BareIndex { head: map![], qual: vec![], owner: vec![], next: vec![] }; }
}

methods BareIndex {
    add &self q:Sym -> void {
        bare: str = lastComponentOf(nameOf(q));
        prev: long = -1;
        hit: Option<long> = self.head.find(bare);
        match hit { Some(i) { prev = i; } None { } }
        self.qual.push(q);
        self.owner.push(moduleOfName(nameOf(q)));
        self.next.push(prev);
        self.head.put(keep(bare), self.qual.len() - 1);
    }

    // The first entry for `bare`, or -1. Walk on with `nextOf`.
    firstOf &self bare:str -> long {
        hit: Option<long> = self.head.find(bare);
        match hit { Some(i) { return i; } None { } }
        return -1;
    }
    nextOf  &self i:long -> long { return self.next.get(i); }
    qualAt  &self i:long -> Sym  { return self.qual.get(i); }
    ownerAt &self i:long -> Sym  { return self.owner.get(i); }
}

// The part of `module::Name` after the separator, or the whole thing if there is none.
pub lastComponentOf q:str -> str {
    i: long = 0;
    cut: long = -1;
    while (i + 1 < q.len) {
        if (charAt(q, i) == ':' && charAt(q, i + 1) == ':') { cut = i; }
        i = i + 1;
    }
    if (cut < 0) { return q; }
    return strSlice(q, cut + 2, q.len - cut - 2);
}

// ─── structs ─────────────────────────────────────────────────────────────────

pub struct FieldDef {
    name: Sym,
    kind: Lit,
    structName: Sym,      // the companion name, when the kind needs one
    offset: long,
    isArray: bool,
    count: long
}

// The placed field and where the next one starts. Returned together rather than advancing the
// cursor through an `inout`, which the language allows only for a struct.
pub struct Placed { field: FieldDef, next: long }

// The aggregates whose declaration is being read right now: registered so the body can name
// them, sized only once it is finished. Declarations do not nest, so this holds at most one.
pub var gTypesInProgress: Vec<Sym>;

pub struct StructDef {
    name: Sym,
    firstField: long, fieldCount: long,
    size: long,
    isEnum: bool          // laid out as a tagged union; the fields are the tag and the payloads
}

// ─── enums ───────────────────────────────────────────────────────────────────

pub struct VariantDef {
    name: Sym,
    value: long,
    firstPayload: long, payloadCount: long
}

pub struct EnumDef {
    name: Sym,
    backing: Lit,                    // the tag's width
    firstVariant: long, variantCount: long,
    hasPayload: bool                 // a sum type rather than a set of integer constants
}

// ─── traits ──────────────────────────────────────────────────────────────────

// A trait's name plus its type arguments: `Iter` unparameterized, `Iter_long` once applied. That
// mangled spelling is what a vtable label and a trait-object companion name are built from.
pub struct TraitRef { name: Sym, firstArg: long, argCount: long }

pub struct TraitMethodSig {
    name: Sym,
    returnKind: Lit, returnName: Sym,
    firstParam: long, paramCount: long,
    isStatic: bool,                  // no receiver: a constructor, so the trait is a bound only
    lentSelf: bool                   // `&self` rather than `self`: what a derived method's receiver is
}

pub struct TraitDef {
    name: Sym,
    firstMethod: long, methodCount: long,
    firstParam: long,  paramCount: long    // its own type parameters
}

// `methods S for T`, which type implements which trait, and with what functions.
pub struct TraitImplDef {
    structName: Sym,
    trait: TraitRef,
    firstFn: long, fnCount: long,
    // A flat (`pub`, argument-free) trait's methods are `Owner_method`, unless another trait's
    // implementation for the same type took one of those names first: then this one's carry the
    // trait (`Owner_Trait_method`, as a parameterized trait's always do). See `flatCarries`.
    carried: bool
}

// ─── globals ─────────────────────────────────────────────────────────────────

pub struct GlobalDef {
    name: Sym,
    kind: Lit,
    structName: Sym,
    isArray: bool,
    count: long,
    visibility: Vis,
    file: Sym,
    pkg: Sym,
    init: NodeId,         // NO_NODE when it is default-initialized
    // A global is immutable unless declared `var`. An immutable one must be computed at compile
    // time (it is an error if it cannot be), is never written afterwards (the checker refuses
    // every write), and is emitted in `.rodata`. A `var` may be initialized at startup and
    // written; it lives in `.data`.
    isVar: bool
}

// ─── aliases ─────────────────────────────────────────────────────────────────

pub struct AliasDef { name: Sym, target: TypeRef, visibility: Vis, file: Sym, pkg: Sym }

// `vt_<Struct>_<Trait>_vtable`. One per implementation, holding the method addresses in the
// trait's declaration order, which is the order a dispatch indexes by. Here rather than beside
// the emitter because both the lowerer (which points at one) and the emitter (which writes one)
// have to agree on the spelling.
pub vtableName concrete:Sym trait:Sym -> str {
    s: String;
    s.pushStr("vt_");
    pushMangled(&s, nameOf(concrete));
    s.push('_');
    pushMangled(&s, nameOf(trait));
    s.pushStr("_vtable");
    return keepString(s);
}

// `::` is not a NASM identifier character, so every symbol this compiler emits (a function label,
// a global, a vtable) spells a module qualifier with `$` instead.
pub pushMangled inout s:String name:str -> void {
    i: long = 0;
    while (i < name.len) {
        c: long = charAt(name, i);
        if (c == ':') {
            s.push('$');
            if (charAt(name, i + 1) == ':') { i = i + 1; }
        } else {
            s.push(c as char);
        }
        i = i + 1;
    }
}

// ─── generic templates ───────────────────────────────────────────────────────
//
// A generic declaration is not a type: it is a pattern for making types. The template is recorded
// here at parse time, and monomorphization stamps out one concrete instance per distinct set of
// type arguments. `params` are the names it binds (`T`, `U`); a field's or a variant payload's
// type may be one of them, which is what `Lit.TypeVar` marks.

pub struct GField { name: Sym, kind: TypeRef, isArray: bool, count: long }

// A generic sum type's variants. The payload types are in `gFields`, named `$V$0`; this is what
// says which variants exist, what each is tagged with, and how many values it carries, which a
// constructor needs before any instance has been stamped.
pub struct GVariant { name: Sym, value: long, payloadCount: long }

// `T_method`: the ordinary function a method becomes.
pub methodName owner:Sym method:Sym -> Sym {
    s: String;
    s.pushStr(nameOf(owner));
    s.push('_');
    s.pushStr(nameOf(method));
    out: Sym = NO_SYM;
    out = internString(s);
    return out;
}

// One `T: Trait<Args>` from a template's parameter list: which parameter, and what it must
// implement. The arguments matter as much as the trait: `count<T, I: Iter<T>>` mentions T nowhere
// else, so the only way to learn what T is, is to see which `Iter` the concrete I implements.
pub struct MethodBound { param: long, trait: TraitRef }

// What kind of thing one template parameter is, beside its name in `gParams`: a type, or a
// length (`N: long`, an array's length and a `long` value in a body), and what it is when a use
// leaves it out (`N: long = 4096`, `A = Heap`; `Lit.Void` when it has no default).
pub struct GParamInfo { isLen: bool, deflt: TypeRef }

pub struct GTemplate {
    name:  Sym,
    firstParam: long, paramCount: long,     // into `gParams`
    firstField: long, fieldCount: long,     // into `gFields`: a struct's fields, an enum's payloads
    firstVariant: long, variantCount: long, // into `gVariants`, for a sum type
    // The bounds on the type's own parameters (`struct Wrap<W: Default>`), which every instance
    // must meet. A methods block's bounds are conditional (an instance that fails one simply has
    // no such method); these are not, so an instance that fails one is an error at the use.
    firstBound: long, boundCount: long,     // into `bounds`
    isEnum: bool,
    visibility: Vis, file: Sym, pkg: Sym
}

// One request to stamp an instance out: the template, and the concrete arguments to substitute.
pub struct GRequest { base: Sym, instance: Sym, firstArg: long, argCount: long }
// One instantiation a call asked for: the template, the name its clone will have, and what its
// type parameters were inferred to be.
pub struct FnRequest { base: Sym, instance: Sym, firstArg: long, argCount: long }

// ─── the tables ──────────────────────────────────────────────────────────────

pub struct Registry {
    structs:   Vec<StructDef>,
    structAt:  HashMap<str, long>,
    structAtSym: HashMap<long, long>,   // the same by the name's Sym: what a caller holding one asks (`findStructSym`)
    fields:    Vec<FieldDef>,

    enums:     Vec<EnumDef>,
    enumAt:    HashMap<str, long>,
    enumAtSym: HashMap<long, long>,     // the same by Sym (`findEnumSym`)
    variants:  Vec<VariantDef>,
    payloads:  Vec<TypeRef>,

    fieldAt2:  HashMap<long, long>,   // (firstField, name) -> the field's index in the run

    traits:    Vec<TraitDef>,
    traitAt:   HashMap<long, long>,     // by the name's number
    traitMethods: Vec<TraitMethodSig>,
    // Every run of type references a trait needs: a declaration's parameters (`firstParam`) and
    // an instantiation's arguments (`firstArg`), which are the same shape and never overlap.
    traitArgs:    Vec<TypeRef>,
    impls:     Vec<TraitImplDef>,
    implFns:   Vec<Sym>,
    implAt2:   HashMap<long, long>,   // (type, trait) -> the first impl; `implNext` chains
    implNext:  Vec<long>,
    // Every implementation's functions by name, for `flatCarries`; and, by type, the
    // implementations that carried their trait for a clash (the first, `carriedNext` chaining
    // the rest), which a method call asks before it looks for an ambiguity.
    implFnSet: HashMap<str, bool>,
    carriedOwners: HashMap<str, long>,
    carriedNext: Vec<long>,
    // The traits a module owns (declared without `pub`: `geo::Shape`), in declaration order. A
    // method call asks its own module's first (`Checker.ownTraitMethod`); few programs have any.
    ownedTraits: Vec<Sym>,
    // What each stamped instantiation instantiates: the base trait and its arguments, found by
    // the instance's name number (`traitInstOf`). An instance is spelled with its arguments
    // (`Fn1_geo::P_long`), so its spelling cannot be split back into a name and arguments.
    traitInsts: Vec<TraitRef>,
    traitInstAt: HashMap<long, long>,

    globals:   Vec<GlobalDef>,
    globalAt:  HashMap<long, long>,     // by the name's number
    macroAt:   HashMap<str, long>,    // the functions declared `macro`, by qualified name
    // `trait T derive m`: the macro that writes `methods X for T` for a type with none, as
    // written, and the file the trait was declared in, which is where that name resolves.
    deriveBy:  HashMap<str, Sym>,
    deriveIn:  HashMap<str, Sym>,
    globalOrder: Vec<Sym>,            // declaration order, which is initialization order

    aliases:   Vec<AliasDef>,
    aliasAt:   HashMap<str, long>,
    // `type Meters = distinct long`: a named scalar registered as an enum with no variants over
    // the base's integer, and here, by name, the type it was declared distinct from. That entry is
    // what makes it convert only by `as` and take operators only through traits.
    distinctBase: HashMap<str, TypeRef>,

    // Every declared type name by its bare component, for `resolveBareIn`. One index covers all
    // five tables: what it is asked is "who declares this name", and which table holds it is a
    // question only the answer needs.
    byBare: BareIndex,

    // A bare name's first declaration in each table, and how far each table has been indexed.
    // There is one index per table because the tables have a precedence (`endsWithName`), and
    // each remembers how far it got because declarations arrive while the program is still
    // being parsed.
    byStructLast: HashMap<str, Sym>, byEnumLast:  HashMap<str, Sym>,
    byTemplateLast: HashMap<str, Sym>, byTraitLast: HashMap<str, Sym>,
    byAliasLast: HashMap<str, Sym>,
    lastStructs: long, lastEnums: long, lastTemplates: long, lastTraits: long, lastAliases: long,

    templates: Vec<GTemplate>,
    templateAt: HashMap<long, long>,    // by the name's number
    gVariants: Vec<GVariant>,
    bounds:    Vec<MethodBound>,
    gParams:   Vec<Sym>,
    gParamInfo: Vec<GParamInfo>,      // parallel to `gParams`
    gFields:   Vec<GField>,
    requests:  Vec<GRequest>,
    requestIx: HashMap<long, long>,   // instance name (its number) -> its request, so asking is not a scan
    gArgs:     Vec<TypeRef>,
    // The structs a closure literal was desugared into (its captures), by the name's number: the
    // parser's own, and every instance requested of a generic one. Asked by name rather than read
    // off the spelling, which an instance ends with its last argument's (`m::$closure0_7_m::P`).
    closureEnvs: HashMap<long, bool>,

    // Requests a dependency's unchecked bodies made, held back (see `request`). `deferIn` is the
    // module whose body the parser is reading when it is one of those, NO_SYM otherwise.
    deferIn:     Sym,
    reqDeferred: Vec<bool>,
    reqPos:      Vec<long>,           // per request, where it was first asked for (`posOf`)
    deferReq:    Vec<long>,           // per module, a chain of the requests its bodies held
    deferNext:   Vec<long>,
    deferHead:   HashMap<str, long>,
    released:    Vec<long>,           // let go since monomorphization last drained

    // While the parser reads its own modules (`journal`), the keys that the sets above holding no
    // index (`macroAt`, `deriveBy` and `deriveIn`, `distinctBase`, `closureEnvs`, `implFnSet`)
    // gained, as pairs of a `KEY_*` tag and the name: what `rewindTo` takes back out of them. A
    // table holding an index needs no record, since its new entries point past the mark.
    journal:     bool,
    added:       Vec<long>
}

local KEY_MACRO: long = 1;
local KEY_DERIVE: long = 2;
local KEY_DISTINCT: long = 3;
local KEY_CLOSURE: long = 4;
local KEY_IMPLFN: long = 5;

// ─── what a `...any` box says, as `stdlib::fmt` reads it ─────────────────────
// The tag a box gets for a kind that `fmt.k`'s own `BoxTag` enum names a variant for (`Bool`).
// It is read from that enum so the compiler and the library cannot disagree; a library without
// the variant gets `dflt`, the tag it has always read that kind with.
pub boxTagOf variant:str dflt:long -> long {
    ei: long = gReg.findEnum(FMT_BOX_TAG);
    if (ei < 0) { return dflt; }
    d: EnumDef = gReg.enumDef(ei);
    vi: long = gReg.findVariant(d, variant);
    if (vi < 0) { return dflt; }
    return gReg.variantAt(d, vi).value;
}
pub FMT_BOX_TAG: str = "fmt::BoxTag";
// A float box's `y` word: the address of `fmt::floatBoxFormat`, when the program has it, so
// only a program that boxes a float reaches (and links) the float formatter. NO_SYM otherwise,
// and `y` is 0. Set by the checker as it indexes the functions.
pub FLOAT_BOX_FORMAT: str = "fmt::floatBoxFormat";
pub var gFloatBoxFormat: Sym = NO_SYM;

// ─── what a stamped call's receiver was bound by ─────────────────────────────
// `x.m()` in a generic body where `x` is a `T: Show`: monomorphization notes, per call it stamps,
// the traits that bound the receiver's type parameter (a run in `gHintTraits` ended by NO_SYM),
// so that when two traits each give the bound type an `m` the checker takes the one the body was
// written against (`Checker.carriedAmbiguity`). Noted only in a program with such a pair.
pub var gCallHints: HashMap<long, long> = map![];
pub var gHintTraits: Vec<Sym> = vec![];

// ─── where an instance came from ─────────────────────────────────────────────
// For an error's "in instantiation of" notes (`parse::diag`): where each generic instance was
// first asked for (a type's, `Vec_String`, or a function's, `vecOf_long`) and which instance's
// code asked for it (NO_SYM when it was code nothing stamped), plus the instance (or derive) each
// stamped function belongs to. `gCtxInst` is the instance whose code is being worked on right
// now: monomorphization sets it while it clones one, and the checker while it types one. This is
// kept beside the registry rather than in it because none of it goes into a `.klib`, so the
// chain for a dependency's instance stops at the dependency.
pub struct Origin { pos: long, parent: Sym, label: Sym }   // label: how a note names it, if not by its type
pub var gCtxInst: Sym = NO_SYM;
local var gOrigins: HashMap<str, Origin> = map![];
local var gFnOwner: HashMap<str, Sym> = map![];

pub noteOrigin inst:Sym pos:long label:Sym -> void {
    if (gOrigins.has(nameOf(inst))) { return; }
    parent: Sym = gCtxInst;
    if (parent == inst) { parent = NO_SYM; }
    gOrigins.put(nameOf(inst), Origin { pos: pos, parent: parent, label: label });
}
// A request taken back with the declaration that made it (`Registry.rewindTo`). While the parser
// runs, only a new request notes an origin, so the request's is the one there.
pub forgetOrigin inst:Sym -> void { gOrigins.remove(nameOf(inst)); }
pub originOf inst:Sym -> Origin {
    hit: Option<Origin> = gOrigins.find(nameOf(inst));
    match hit { Some(o) { return o; } None { } }
    return Origin { pos: 0, parent: NO_SYM, label: NO_SYM };
}
pub noteFnOwner fn:Sym owner:Sym -> void { gFnOwner.put(nameOf(fn), owner); }
pub fnOwnerOf fn:Sym -> Sym {
    if (fn == NO_SYM) { return NO_SYM; }
    hit: Option<Sym> = gFnOwner.find(nameOf(fn));
    match hit { Some(o) { return o; } None { } }
    return NO_SYM;
}
// A phase starting on a function: the error path's context (`gCtxFn`), and the instance its
// requests are made on behalf of.
pub enterFn fn:Sym -> void {
    gCtxFn = fn;
    gCtxInst = fnOwnerOf(fn);
}
// Where each function is defined, for a later phase that no longer holds the tree (the emitter):
// recorded as the lowerer meets each one.
local var gFnPos: HashMap<str, long> = map![];
pub noteFnPos fn:Sym pos:long -> void { if (pos != 0) { gFnPos.put(nameOf(fn), pos); } }
pub fnPosOf fn:Sym -> long {
    hit: Option<long> = gFnPos.find(nameOf(fn));
    match hit { Some(p) { return p; } None { } }
    return 0;
}
// The emitter starting on a function: its context, and its definition as the position.
pub enterFnAtDef fn:Sym -> void {
    enterFn(fn);
    gPos = fnPosOf(fn);
}

// The keys the two indexes below are built on: two numbers packed into one word. A struct's field
// run identifies the struct (the run never moves once appended), so a field needs no copy of its
// owner's name; an implementation is keyed by its type's name and its trait's, each a `Sym`.
// String keys would have to be built and interned for every lookup, and the registry is asked
// once per field access and once per "does it implement".
local fieldKey firstField:long name:Sym -> long {
    return (firstField << 32) | (name as long);
}
local implKey structName:Sym trait:Sym -> long {
    return ((structName as long) << 32) | (trait as long);
}

// Lookups in one last-component index. These are free functions rather than methods because
// `self.f(&self.map, ..)` would lend `self` mutably while one of its fields is lent as well,
// which exclusivity (rightly) refuses.
local lastHit inout m:HashMap<str, Sym> bare:str -> Sym {
    hit: Option<Sym> = m.find(bare);
    match hit { Some(n) { return n; } None { } }
    return NO_SYM;
}
local noteLast inout m:HashMap<str, Sym> n:Sym -> void {
    key: str = lastComponentOf(nameOf(n));
    if (!m.has(key)) { m.put(key, n); }
}

methods Registry for Default {
    new -> Registry {
        return Registry { structs: vec![], structAt: map![], structAtSym: map![], fields: vec![],
                          enums: vec![], enumAt: map![], enumAtSym: map![], variants: vec![], payloads: vec![],
                          fieldAt2: map![],
                          traits: vec![], traitAt: map![], traitMethods: vec![],
                          traitArgs: vec![], impls: vec![], implFns: vec![],
                          implAt2: map![], implNext: vec![], implFnSet: map![], carriedOwners: map![],
                          carriedNext: vec![], ownedTraits: vec![], traitInsts: vec![], traitInstAt: map![],
                          globals: vec![], globalAt: map![], macroAt: map![],
                          deriveBy: map![], deriveIn: map![], globalOrder: vec![],
                          aliases: vec![], aliasAt: map![], distinctBase: map![],
                          byBare: BareIndex.new(),
                          byStructLast: map![], byEnumLast: map![], byTemplateLast: map![],
                          byTraitLast: map![], byAliasLast: map![],
                          lastStructs: 0, lastEnums: 0, lastTemplates: 0,
                          lastTraits: 0, lastAliases: 0,
                          templates: vec![], templateAt: map![], gVariants: vec![], bounds: vec![],
                          gParams: vec![], gParamInfo: vec![], gFields: vec![],
                          requests: vec![], requestIx: map![], gArgs: vec![], closureEnvs: map![],
                          deferIn: NO_SYM, reqDeferred: vec![], reqPos: vec![], deferReq: vec![], deferNext: vec![],
                          deferHead: map![], released: vec![], journal: false, added: vec![] };
    }
}

methods Registry {
    // ─── structs ─────────────────────────────────────────────────────────────

    // Append `fs` as one run and register the struct. Returns its index.
    addStruct &self name:Sym fs:Vec<FieldDef> size:long isEnum:bool -> long {
        first: long = self.fields.len();
        self.fields.extend(fs);
        for k in 0..fs.len() {
            self.fieldAt2.put(fieldKey(first, fs.get(k).name), k);
        }
        self.structs.push(StructDef { name: name, firstField: first, fieldCount: fs.len(),
                                      size: size, isEnum: isEnum });
        idx: long = self.structs.len() - 1;
        self.structAt.put(nameOf(name), idx);
        self.structAtSym.put(name as long, idx);
        return idx;
    }
    // A struct is registered before its body is read, as a placeholder with no fields and no size,
    // so the body can name the type it is declaring: `kids: Box<Tree>` or `next: *Tree` inside
    // `Tree`. Eight bytes either way, so neither needs the size, and `typeSizeOf` refuses anything
    // that does, which is exactly a direct `kids: Tree`, infinitely large. `finishStruct` writes
    // the real layout at the `}`; `abandonStruct` retracts a placeholder that turned out not to be
    // an aggregate at all (a backed enum).
    beginStruct &self name:Sym -> long {
        self.structs.push(StructDef { name: name, firstField: self.fields.len(), fieldCount: 0,
                                      size: 0, isEnum: false });
        idx: long = self.structs.len() - 1;
        self.structAt.put(nameOf(name), idx);
        self.structAtSym.put(name as long, idx);
        gTypesInProgress.push(name);
        return idx;
    }
    finishStruct &self idx:long fs:Vec<FieldDef> size:long isEnum:bool -> void {
        first: long = self.fields.len();
        self.fields.extend(fs);
        for k in 0..fs.len() {
            self.fieldAt2.put(fieldKey(first, fs.get(k).name), k);
        }
        d: StructDef = self.structs.get(idx);
        self.structs.set(idx, StructDef { name: d.name, firstField: first, fieldCount: fs.len(),
                                          size: size, isEnum: isEnum });
        gTypesInProgress.pop();
    }
    abandonStruct &self idx:long -> void {
        d: StructDef = self.structs.get(idx);
        self.structAt.remove(nameOf(d.name));
        self.structAtSym.remove(d.name as long);
        gTypesInProgress.pop();
    }

    findStruct &self q:str -> long {
        hit: Option<long> = self.structAt.find(q);
        match hit { Some(i) { return i; } None { } }
        return NOT_FOUND;
    }
    findStructSym &self n:Sym -> long {
        hit: Option<long> = self.structAtSym.find(n as long);
        match hit { Some(i) { return i; } None { } }
        return NOT_FOUND;
    }
    hasStruct &self q:str -> bool { return self.findStruct(q) >= 0; }
    hasStructSym &self n:Sym -> bool { return self.findStructSym(n) >= 0; }
    structDef &self i:long -> StructDef { return self.structs.get(i); }
    structCount &self -> long { return self.structs.len(); }
    // Re-place a struct's fields from the sizes its field types have now. A struct is laid out
    // when it is parsed, and a field naming a generic instance had no size then (nothing had
    // stamped it), so it took zero bytes and every field after it landed on top of it. Returns
    // whether anything actually moved, which is what lets the caller repeat to a fixpoint.
    relayoutStruct &self i:long -> bool {
        d: StructDef = self.structs.get(i);
        if (d.isEnum) { return self.relayoutSum(i, d); }
        cursor: long = 0;
        moved: bool = false;
        for k in 0..d.fieldCount {
            f: FieldDef = self.fields.get(d.firstField + k);
            p: Placed = self.placeFieldIn(cursor, f);
            if (p.field.offset != f.offset) { moved = true; }
            self.fields.set(d.firstField + k, p.field);
            cursor = p.next;
        }
        size: long = alignUp(cursor, 8);
        if (size != d.size) { moved = true; }
        d.size = size;
        self.structs.set(i, d);
        return moved;
    }

    // A sum type is relaid the way `layoutEnum` laid it: every variant's payloads from the same
    // offset, the size the widest variant's. Its fields are the tag followed by the payloads in
    // declaration order, so a variant's `firstPayload` is one past the tag. This is what sizes
    // `Many(Vec<Tree>)` inside `Tree`: `Vec<Tree>` had no size while `Tree` was being read.
    relayoutSum &self i:long d:StructDef -> bool {
        e: long = self.findEnumSym(d.name);
        if (e < 0) { return false; }
        ed: EnumDef = self.enumDef(e);
        tagSize: long = typeInfo(ed.backing).size;
        maxAlign: long = tagSize;
        for k in 1..d.fieldCount {
            f: FieldDef = self.fields.get(d.firstField + k);
            a: long = self.typeSizeIn(f.kind, f.structName);
            if (isAggregate(f.kind)) { a = 8; }
            if (a > maxAlign) { maxAlign = a; }
        }
        payloadOffset: long = alignUp(tagSize, maxAlign);
        end: long = tagSize;
        moved: bool = false;
        for v in 0..ed.variantCount {
            var: VariantDef = self.variantAt(ed, v);
            cursor: long = payloadOffset;
            for j in 0..var.payloadCount {
                at: long = d.firstField + 1 + var.firstPayload + j;
                f: FieldDef = self.fields.get(at);
                p: Placed = self.placeFieldIn(cursor, f);
                if (p.field.offset != f.offset) { moved = true; }
                self.fields.set(at, p.field);
                cursor = p.next;
            }
            if (cursor > end) { end = cursor; }
        }
        size: long = alignUp(end, 8);
        if (size != d.size) { moved = true; }
        relaid: StructDef = d;
        relaid.size = size;
        self.structs.set(i, relaid);
        return moved;
    }
    fieldAt &self d:StructDef k:long -> FieldDef { return self.fields.get(d.firstField + k); }

    // A field by name, or NOT_FOUND. It is keyed on where the struct's run starts in the flat
    // `fields` vector together with the name (`fieldKey`), which identifies the field without
    // building a key from the struct's own name, and stays valid because a struct's run never
    // moves once appended. This is not a handful-of-fields lookup: the checker asks it per field
    // access, per struct literal initializer and per drop-glue walk, over structs with dozens of
    // fields.
    findField &self d:StructDef name:str -> long { return self.findFieldSym(d, intern(name)); }
    // The same for a name already interned: what nearly every caller holds.
    findFieldSym &self d:StructDef name:Sym -> long {
        hit: Option<long> = self.fieldAt2.find(fieldKey(d.firstField, name));
        match hit { Some(k) { return k; } None { } }
        return NOT_FOUND;
    }

    // ─── enums ───────────────────────────────────────────────────────────────

    addEnum &self name:Sym backing:Lit vs:Vec<VariantDef> hasPayload:bool -> long {
        first: long = self.variants.len();
        self.variants.extend(vs);
        self.enums.push(EnumDef { name: name, backing: backing,
                                  firstVariant: first, variantCount: vs.len(),
                                  hasPayload: hasPayload });
        idx: long = self.enums.len() - 1;
        self.enumAt.put(nameOf(name), idx);
        self.enumAtSym.put(name as long, idx);
        return idx;
    }
    findEnum &self q:str -> long {
        hit: Option<long> = self.enumAt.find(q);
        match hit { Some(i) { return i; } None { } }
        return NOT_FOUND;
    }
    findEnumSym &self n:Sym -> long {
        hit: Option<long> = self.enumAtSym.find(n as long);
        match hit { Some(i) { return i; } None { } }
        return NOT_FOUND;
    }
    isEnumType &self q:str -> bool { return self.findEnum(q) >= 0; }
    isEnumTypeSym &self n:Sym -> bool { return self.findEnumSym(n) >= 0; }
    // A distinct type's base (`type Meters = distinct long` -> long), recorded once its enum is.
    addDistinct &self name:Sym base:TypeRef -> void {
        if (self.journal && !self.distinctBase.has(nameOf(name))) { self.noteAdded(KEY_DISTINCT, name); }
        self.distinctBase.put(nameOf(name), base);
    }
    // The base of the distinct type `n`, or `Lit.Void` when `n` is not one.
    distinctOf &self n:Sym -> TypeRef {
        if (n == NO_SYM || self.distinctBase.len() == 0) { return TypeRef { base: Lit.Void, name: NO_SYM }; }
        hit: Option<TypeRef> = self.distinctBase.find(nameOf(n));
        match hit { Some(t) { return t; } None { } }
        return TypeRef { base: Lit.Void, name: NO_SYM };
    }
    isDistinct &self n:Sym -> bool { return self.distinctOf(n).base != Lit.Void; }
    // A sum type (an aggregate) as opposed to a set of integer constants.
    isSumType &self q:str -> bool {
        i: long = self.findEnum(q);
        if (i < 0) { return false; }
        return self.enums.get(i).hasPayload;
    }
    enumDef &self i:long -> EnumDef { return self.enums.get(i); }
    variantAt &self d:EnumDef k:long -> VariantDef { return self.variants.get(d.firstVariant + k); }
    findVariant &self d:EnumDef name:str -> long {
        for k in 0..d.variantCount {
            if (nameOf(self.variants.get(d.firstVariant + k).name) == name) { return k; }
        }
        return NOT_FOUND;
    }

    // ─── traits ──────────────────────────────────────────────────────────────

    addTraitArgs &self items:Vec<TypeRef> -> long {
        first: long = self.traitArgs.len();
        self.traitArgs.extend(items);
        return first;
    }
    traitArgAt &self t:TraitRef k:long -> TypeRef { return self.traitArgs.get(t.firstArg + k); }

    // `Iter` when unparameterized, `Iter_long` once it is: the spelling a vtable label and a
    // trait-object companion name are built from.
    traitMangled &self t:TraitRef -> str {
        s: String;
        s.pushStr(nameOf(t.name));
        for k in 0..t.argCount {
            a: TypeRef = self.traitArgAt(t, k);
            s.push('_');
            s.pushStr(typeMangleName(a.base, a.name));
        }
        out: str = "";
        out = keepString(s);
        return out;
    }

    traitRefEq &self a:TraitRef b:TraitRef -> bool {
        if (a.name != b.name || a.argCount != b.argCount) { return false; }
        for k in 0..a.argCount {
            if (self.traitArgAt(a, k) != self.traitArgAt(b, k)) { return false; }
        }
        return true;
    }

    // Where a method sits in a trait's vtable: its index in declaration order, which is the
    // order `addImpl` recorded the implementing functions in. -1 if the trait has no such method.
    methodSlot &self t:TraitDef name:str -> long {
        for k in 0..t.methodCount {
            if (nameOf(self.traitMethods.get(t.firstMethod + k).name) == name) { return k; }
        }
        return NOT_FOUND;
    }
    traitDef &self i:long -> TraitDef { return self.traits.get(i); }
    // Do an already-registered trait and a freshly-read set of signatures describe the same
    // trait? Re-declaring one is legal and routine: a file writes `trait Drop { drop &self ->
    // void; }` rather than pulling in <core>, and a dozen tests do, so an identical repeat is
    // kept silently. A different trait under the same name is a genuine conflict, not something
    // to settle by keeping whichever module happened to be parsed first.
    sameTrait &self d:TraitDef sigs:Vec<TraitMethodSig> nparams:long -> bool {
        if (d.methodCount != sigs.len() || d.paramCount != nparams) { return false; }
        for k in 0..sigs.len() {
            a: TraitMethodSig = self.traitMethodAt(d, k);
            b: TraitMethodSig = sigs.get(k);
            if (a.name != b.name || a.returnKind != b.returnKind || a.returnName != b.returnName
                || a.paramCount != b.paramCount || a.isStatic != b.isStatic) { return false; }
        }
        return true;
    }

    // `Iter<long>` used as a type stamps a concrete trait of that name, with the template's
    // parameters substituted through every method signature. Everything downstream then deals
    // only in concrete traits (one vtable per instance, one set of signatures) exactly as a
    // generic struct is laid out before anything reads its fields. Idempotent: a second use of
    // the same instantiation finds the first.
    stampTrait &self base:Sym args:Vec<TypeRef> -> Sym {
        at: long = self.findTraitSym(base);
        if (at < 0) { return base; }
        d: TraitDef = self.traits.get(at);
        if (d.paramCount == 0 || args.len() != d.paramCount) { return base; }
        ref: TraitRef = TraitRef { name: base, firstArg: self.addTraitArgs(args), argCount: args.len() };
        inst: Sym = intern(self.traitMangled(ref));
        if (self.findTraitSym(inst) >= 0) { return inst; }

        sigs: Vec<TraitMethodSig>;
        for k in 0..d.methodCount {
            m: TraitMethodSig = self.traitMethods.get(d.firstMethod + k);
            r: TypeRef = self.substTraitType(d, args, m.returnKind, m.returnName);
            m.returnKind = r.base;
            m.returnName = r.name;
            sigs.push(m);
        }
        firstMethod: long = self.traitMethods.len();
        self.traitMethods.extend(sigs);
        self.traits.push(TraitDef { name: inst, firstMethod: firstMethod,
                                    methodCount: sigs.len(), firstParam: 0, paramCount: 0 });
        self.traitAt.put(inst as long, self.traits.len() - 1);
        self.traitInsts.push(ref);
        self.traitInstAt.put(inst as long, self.traitInsts.len() - 1);
        return inst;
    }
    // The base trait and arguments a stamped instance was made from, or -1 for a trait that is
    // no instance; `traitInstRef` reads it.
    traitInstOf &self t:Sym -> long {
        if (self.traitInstAt.isEmpty()) { return NOT_FOUND; }
        hit: Option<long> = self.traitInstAt.find(t as long);
        match hit { Some(i) { return i; } None { } }
        return NOT_FOUND;
    }
    traitInstRef &self i:long -> TraitRef { return self.traitInsts.get(i);
    }

    // One type from a trait's signature under an instantiation's arguments: a parameter becomes
    // what stands in its place, anything else is itself.
    substTraitType &self d:TraitDef args:Vec<TypeRef> k:Lit n:Sym -> TypeRef {
        if (k != Lit.TypeVar) { return TypeRef { base: k, name: n }; }
        for i in 0..d.paramCount {
            if (self.traitArgs.get(d.firstParam + i).name == n) { return args.get(i); }
        }
        return TypeRef { base: k, name: n };
    }
    traitMethodAt &self t:TraitDef k:long -> TraitMethodSig {
        return self.traitMethods.get(t.firstMethod + k);
    }

    // The functions `S` implements `t` with, in vtable order. Empty when it does not.
    implFnsOf &self s:Sym t:Sym -> Vec<Sym> {
        out: Vec<Sym>;
        hit: Option<long> = self.implAt2.find(implKey(s, t));
        match hit {
            Some(i) {
                im: TraitImplDef = self.impls.get(i);
                for k in 0..im.fnCount { out.push(self.implFns.get(im.firstFn + k)); }
            }
            None { }
        }
        return out;
    }

    // The first implementation of trait `t` (by its base name) for `s`, or -1; `nextImplOf` walks
    // the rest, the same trait at other arguments.
    firstImplOf &self s:Sym t:Sym -> long {
        hit: Option<long> = self.implAt2.find(implKey(s, t));
        match hit { Some(i) { return i; } None { } }
        return NOT_FOUND;
    }
    nextImplOf &self i:long -> long { return self.implNext.get(i); }

    // Every (struct, trait) pair that has an implementation, for emitting one vtable each.
    implCount &self -> long { return self.impls.len(); }
    // Whether a concrete type is known to implement a trait. `Copy` and `Clone` are markers the
    // compiler derives rather than impls anyone writes, so nothing is registered for them.
    structImplements &self s:str t:Sym -> bool {
        return self.implAt2.has(implKey(intern(s), t));
    }
    implFnAt &self im:TraitImplDef k:long -> Sym { return self.implFns.get(im.firstFn + k); }
    implAt &self i:long -> TraitImplDef { return self.impls.get(i); }
    // Whether `f` is a method of some implementation: a function a vtable may hold.
    isImplFn &self f:Sym -> bool { return self.implFnSet.has(nameOf(f)); }

    findTrait &self q:str -> long { return self.findTraitSym(symIfAny(q)); }
    findTraitSym &self n:Sym -> long {
        hit: Option<long> = self.traitAt.find(n as long);
        match hit { Some(i) { return i; } None { } }
        return NOT_FOUND;
    }

    // Registers an implementation whose functions are its type's plain `Owner_method`s (or carry
    // the name of a trait that always carries it; see `implFnNameAs`). An implementation whose
    // functions `implFnName` named before it was registered has to pass on what that chose:
    // `addImplAs(..., flatCarries(...))`.
    addImpl &self structName:Sym t:TraitRef fns:Vec<Sym> -> void {
        self.addImplAs(structName, t, fns, false);
    }
    addImplAs &self structName:Sym t:TraitRef fns:Vec<Sym> carried:bool -> void {
        first: long = self.implFns.len();
        self.implFns.extend(fns);
        for f in fns {
            if (self.journal && !self.implFnSet.has(nameOf(f))) { self.noteAdded(KEY_IMPLFN, f); }
            self.implFnSet.put(nameOf(f), true);
        }
        self.impls.push(TraitImplDef { structName: structName, trait: t,
                                       firstFn: first, fnCount: fns.len(), carried: carried });
        self.carriedNext.push(NOT_FOUND);
        if (carried && !self.carriesName(t)) {
            c: long = self.impls.len() - 1;
            ch: Option<long> = self.carriedOwners.find(nameOf(structName));
            match ch {
                Some(head) {
                    j: long = head;
                    while (self.carriedNext.get(j) >= 0) { j = self.carriedNext.get(j); }
                    self.carriedNext.set(j, c);
                }
                None { self.carriedOwners.put(nameOf(structName), c); }
            }
        }
        // Keyed by (type, trait name). A parameterized trait can be implemented more than once
        // for one type, so a repeat is chained behind the first rather than replacing it: the
        // first still answers "does it implement this trait at all", which is the common ask.
        at: long = self.impls.len() - 1;
        key: long = implKey(structName, t.name);
        self.implNext.push(NOT_FOUND);
        hit: Option<long> = self.implAt2.find(key);
        match hit {
            Some(head) {
                j: long = head;
                while (self.implNext.get(j) >= 0) { j = self.implNext.get(j); }
                self.implNext.set(j, at);
            }
            None { self.implAt2.put(key, at); }
        }
    }

    // Does `s` implement `t`? Compared on the whole reference, so an argument-carrying trait
    // matches only the same instantiation.
    implementsTrait &self s:Sym t:TraitRef -> bool {
        hit: Option<long> = self.implAt2.find(implKey(s, t.name));
        match hit {
            Some(i) {
                if (self.traitRefEq(self.impls.get(i).trait, t)) { return true; }
                // Several impls of one parameterized trait for one type (`String` is both
                // `Eq<str>` and `Eq<String>`) share a key, so the rest are chained.
                j: long = self.implNext.get(i);
                while (j >= 0) {
                    if (self.traitRefEq(self.impls.get(j).trait, t)) { return true; }
                    j = self.implNext.get(j);
                }
            }
            None { }
        }
        return false;
    }
    // The impl behind a trait object's vtable: the one for `concrete` whose trait instantiation
    // mangles to `mangled`, the spelling `vtableName` is built from. This is a scan, because the
    // key table is by the trait's bare name and a mangled instantiation cannot be split back into
    // name and arguments without guessing; dispatch at compile time is rare enough not to mind.
    findImplMangled &self concrete:Sym mangled:Sym -> long {
        for i in 0..self.impls.len() {
            im: TraitImplDef = self.impls.get(i);
            if (im.structName == concrete && self.traitMangled(im.trait) == nameOf(mangled)) { return i; }
        }
        return NOT_FOUND;
    }
    // Makes sure the (concrete, trait) impl a trait object names is registered, so that its vtable
    // is emitted. The lowerer's `noteTraitImpl` does the same for the coercions it makes itself.
    ensureImpl &self concrete:Sym trait:Sym -> void {
        if (concrete == NO_SYM || trait == NO_SYM) { return; }
        tr: TraitRef = TraitRef { name: trait, firstArg: 0, argCount: 0 };
        if (self.implementsTrait(concrete, tr)) { return; }
        at: long = self.findTraitSym(trait);
        if (at < 0) { return; }
        t: TraitDef = self.traitDef(at);
        fns: Vec<Sym>;
        carried: bool = self.flatCarries(concrete, tr);
        for k in 0..t.methodCount {
            fns.push(self.implFnNameIn(concrete, tr, self.traitMethodAt(t, k).name, carried));
        }
        self.addImplAs(concrete, tr, fns, carried);
    }
    // Whether `s`'s implementation of the flat trait `t` names its methods after the trait. A
    // registered one says (`carried`); one not registered yet does when another trait's
    // implementation for `s` already has a method of a name `t` declares: two `pub` traits sharing
    // a method name, each implemented for one type. The first keeps `S_m`, the second is `S_T_m`,
    // and a call `x.m()` that cannot tell them apart says so (`Checker.carriedAmbiguity`). A core
    // trait never carries: its methods' names are built by hand all over the compiler.
    flatCarries &self s:Sym t:TraitRef -> bool {
        if (t.name == NO_SYM || self.carriesName(t)) { return false; }
        i: long = self.firstImplOf(s, t.name);
        if (i >= 0) { return self.impls.get(i).carried; }
        // Nor does a callable's `FnN` at its arguments (`Fn0_long`), which a closure implements
        // with the one `call` its `FnN` has.
        tn: str = nameOf(t.name);
        if (isCoreTraitName(tn) || (strStartsWith(tn, "Fn") && tn.len > 2 && isDigit(charAt(tn, 2)))) { return false; }
        ti: long = self.findTraitSym(t.name);
        if (ti < 0) { return false; }
        td: TraitDef = self.traitDef(ti);
        for k in 0..td.methodCount {
            m: Sym = self.traitMethodAt(td, k).name;
            if (self.implFnSet.has(nameOf(methodName(s, m)))) { return true; }
            // A method a core trait also declares: the core trait's implementation keeps the plain
            // name whichever comes first (the compiler builds `T_drop`, `T_new`... by hand), so this
            // one carries its trait's even when nothing has clashed yet. Decided from the core
            // traits alone, which every program has read first, so the choice does not depend on
            // which implementation a module (or another package) writes first.
            if (self.coreMethodNamed(m)) { return true; }
        }
        return false;
    }

    // Whether a core trait declares a method of this name.
    coreMethodNamed &self m:Sym -> bool {
        if (!gCoreMethodsBuilt) {
            names: Vec<str> = gCoreTraits.keys();
            for tn in names {
                ti: long = self.findTrait(tn);
                if (ti < 0) { continue; }
                td: TraitDef = self.traitDef(ti);
                for k in 0..td.methodCount { gCoreMethods.put(nameOf(self.traitMethodAt(td, k).name), true); }
            }
            // Built once the core traits are declared (stdlib/core.k is read first in every
            // program); asked before then, it answers from what there is and asks again.
            gCoreMethodsBuilt = !gCoreMethods.isEmpty();
        }
        return gCoreMethods.has(nameOf(m));
    }
    // The implementations of `s` that carried their trait for a clash: the first, then the chain.
    firstCarriedOf &self s:Sym -> long {
        if (self.carriedOwners.isEmpty()) { return NOT_FOUND; }
        hit: Option<long> = self.carriedOwners.find(nameOf(s));
        match hit { Some(i) { return i; } None { } }
        return NOT_FOUND;
    }
    nextCarriedOf &self i:long -> long { return self.carriedNext.get(i); }

    // The common case: a trait named bare, with no arguments.
    implementsNamed &self s:Sym t:str -> bool {
        return self.implementsTrait(s, TraitRef { name: intern(t), firstArg: 0, argCount: 0 });
    }
    // The same for a trait whose name the caller holds.
    implementsSym &self s:Sym t:Sym -> bool {
        return self.implementsTrait(s, TraitRef { name: t, firstArg: 0, argCount: 0 });
    }

    // A struct needs Drop if it implements it directly, or transitively holds a field that does:
    // drop glue is synthesized for the latter. The recursion terminates because a field is
    // declared before its owner, so a value type cannot contain itself.
    //
    // For an instance of a template the template is asked as well, because whether it owns
    // something is fixed by its declaration, not by how far monomorphization has got. Asking only
    // what has been registered for the instance would answer "no" for `Vec<Tree>` while it is
    // being stamped (its `Drop` is registered after its methods), and so also for a `Tree` that
    // holds one. `Tree` would then count as `Copy`, and `methods Vec<T: Copy>` would be stamped
    // and checked for `Vec<Tree>`. A type that reaches itself only through templates that release
    // nothing does not need Drop; the depth bound is what decides that.
    needsDrop &self s:Sym -> bool { return self.needsDropAt(s, 0); }
    needsDropAt &self s:Sym depth:long -> bool {
        if (s == NO_SYM || depth > 32) { return false; }
        if (self.implementsSym(s, dropName())) { return true; }
        r: long = self.findRequestSym(s);
        if (r >= 0 && self.implementsSym(self.requestAt(r).base, dropName())) { return true; }
        at: long = self.findStructSym(s);
        if (at < 0) {
            if (r < 0) { return false; }
            return self.templateOwns(self.requestAt(r), depth + 1);
        }
        d: StructDef = self.structs.get(at);
        for k in 0..d.fieldCount {
            f: FieldDef = self.fields.get(d.firstField + k);
            if (f.kind == Lit.Struct && self.needsDropAt(f.structName, depth + 1)) { return true; }
        }
        return false;
    }
    // Whether an instance not stamped yet owns something, decided from its template's fields at
    // its arguments. A field that is a parameter owns what its argument owns, a field naming a
    // type owns what that type owns, and one naming another instance over the parameters
    // (`v: Vec<T>`) owns what that template owns.
    templateOwns &self r:GRequest depth:long -> bool {
        ti: long = self.findTemplateSym(r.base);
        if (ti < 0 || depth > 32) { return false; }
        t: GTemplate = self.templateDef(ti);
        for k in 0..t.fieldCount {
            g: GField = self.gFieldAt(t, k);
            if (g.kind.base == Lit.TypeVar) {
                p: long = self.gParamIndex(t, g.kind.name);
                if (p >= 0 && p < r.argCount) {
                    arg: TypeRef = self.gArgAt(r, p);
                    if (arg.base == Lit.Struct && self.needsDropAt(arg.name, depth + 1)) { return true; }
                }
            } else if (g.kind.base == Lit.Struct && self.needsDropAt(g.kind.name, depth + 1)) {
                return true;
            }
        }
        return false;
    }

    // `Copy`: the compiler-derived marker for a freely duplicable value: every scalar, and every
    // struct that does not need Drop, since a bitwise copy of an owning value would release twice.
    isCopy &self k:Lit n:Sym -> bool {
        if (k == Lit.Struct) { return !self.needsDrop(n); }
        if (k == Lit.TypeVar || k == Lit.Void) { return false; }
        return true;   // scalars, views, function and raw pointers: all plain bits
    }

    // Why the struct `s` has no `Clone`, or "" when it has one. It has one when it is written
    // (`methods S for Clone`), stamped for an instance whose bound held, or derivable. A type
    // that owns nothing is `Copy`, and its clone is the copy. Otherwise a derived clone copies
    // what is plain and clones what owns, field by field, so it exists exactly when that makes a
    // real duplicate. It never does for a type with a `drop` of its own (what it owns sits behind
    // its own pointers, which a field-wise copy would share, and both values would release them),
    // nor past a raw pointer (the copy would point at what the original does) or a field that has
    // no `Clone` itself. It is decided from the declarations alone, so the checker refusing a call
    // and monomorphization deciding a `T: Clone` bound give the same answer.
    //
    // The reason is a lowercase clause that the checker prints after `note: `, with names in
    // backticks. When a field is the reason, the field's own reason follows it after a colon.
    //
    // A recursive type (`enum Tree { Leaf(long), Many(Vec<Tree>) }`) is decided coinductively:
    // a type already being asked about counts as having one, and an instance of a generic type
    // whose template implements `Clone` (`methods Vec<T: Clone> for Clone`) has one when its type
    // arguments do, whether or not that instance's implementation is stamped yet.
    cloneBlocker &self s:Sym -> str {
        visiting: Vec<Sym>;
        return self.cloneBlockerIn(s, &visiting);
    }
    cloneBlockerIn &self s:Sym inout visiting:Vec<Sym> -> str {
        if (s == NO_SYM) { return ""; }
        if (self.structImplements(nameOf(s), intern("Clone"))) { return ""; }
        if (!self.needsDrop(s)) { return ""; }
        for k in 0..visiting.len() { if (visiting.get(k) == s) { return ""; } }
        if (self.structImplements(nameOf(s), intern("Drop")) && !self.cloneByTemplate(s)) {
            return "it owns a resource (it implements `Drop`)";
        }
        visiting.push(s);
        why: str = self.cloneBlockerOf(s, &visiting);
        visiting.pop();
        return why;
    }
    // An instance of a generic type whose template writes its own `Clone`: its clone is that one,
    // stamped, and never a derived one.
    cloneByTemplate &self s:Sym -> bool {
        r: long = self.findRequestSym(s);
        return r >= 0 && self.structImplements(nameOf(self.requestAt(r).base), intern("Clone"));
    }
    cloneBlockerOf &self s:Sym inout visiting:Vec<Sym> -> str {
        // An instance whose template implements Clone: its own implementation's bound is on the
        // type arguments, so they are what is asked.
        if (self.cloneByTemplate(s)) {
            req: GRequest = self.requestAt(self.findRequestSym(s));
            for k in 0..req.argCount {
                t: TypeRef = self.gArgAt(req, k);
                if (t.base == Lit.Struct && t.name != NO_SYM) {
                    inner: str = self.cloneBlockerIn(t.name, &visiting);
                    if (inner.len > 0) { return keepString(format("its element type `{}` has no `Clone`: {}", nameOf(t.name), inner)); }
                } else if (t.base == Lit.TraitObj || t.base == Lit.TypeVar) {
                    return keepString(format("its element type `{}` has no `Clone`", nameOf(t.name)));
                }
            }
            return "";
        }
        at: long = self.findStructSym(s);
        if (at < 0) { return ""; }
        d: StructDef = self.structs.get(at);
        for k in 0..d.fieldCount {
            f: FieldDef = self.fields.get(d.firstField + k);
            if (f.kind == Lit.Ptr) {
                return keepString(format("{} is a raw pointer, and a copy would point at what the original does",
                                         cloneFieldLabel(d, f.name)));
            }
            if (f.kind == Lit.Struct && self.needsDrop(f.structName)) {
                // An array of owning elements is cloned element by element, so it has a clone
                // exactly when its element does.
                inner: str = self.cloneBlockerIn(f.structName, &visiting);
                if (inner.len > 0) {
                    return keepString(format("{} (`{}`) has no `Clone`: {}", cloneFieldLabel(d, f.name),
                                             nameOf(f.structName), inner));
                }
            }
        }
        return "";
    }

    // ─── globals ─────────────────────────────────────────────────────────────

    addGlobal &self g:GlobalDef -> void {
        self.globals.push(g);
        self.globalAt.put(g.name as long, self.globals.len() - 1);
        self.globalOrder.push(g.name);
    }
    findGlobal &self q:str -> long { return self.findGlobalSym(symIfAny(q)); }
    findGlobalSym &self n:Sym -> long {
        hit: Option<long> = self.globalAt.find(n as long);
        match hit { Some(i) { return i; } None { } }
        return NOT_FOUND;
    }
    globalDef &self i:long -> GlobalDef { return self.globals.get(i); }
    globalCount &self -> long { return self.globals.len(); }

    // ─── macros ──────────────────────────────────────────────────────────────
    // A `macro` is a function the compiler runs; by its qualified name.
    noteMacro &self q:Sym -> void {
        if (self.journal && !self.macroAt.has(nameOf(q))) { self.noteAdded(KEY_MACRO, q); }
        self.macroAt.put(nameOf(q), 1);
    }
    isMacro &self q:Sym -> bool { return self.macroAt.has(nameOf(q)); }

    // ─── derives ─────────────────────────────────────────────────────────────
    // `trait Encode derive deriveEncode { ... }`: the macro, as written, and the file whose
    // module it resolves in. NO_SYM for a trait with no derive.
    noteDerive &self trait:Sym m:Sym file:Sym -> void {
        if (self.journal && !self.deriveBy.has(nameOf(trait))) { self.noteAdded(KEY_DERIVE, trait); }
        self.deriveBy.put(nameOf(trait), m);
        self.deriveIn.put(nameOf(trait), file);
    }
    deriveMacroOf &self trait:Sym -> Sym {
        hit: Option<Sym> = self.deriveBy.find(nameOf(trait));
        match hit { Some(m) { return m; } None { } }
        return NO_SYM;
    }
    deriveFileOf &self trait:Sym -> Sym {
        hit: Option<Sym> = self.deriveIn.find(nameOf(trait));
        match hit { Some(f) { return f; } None { } }
        return NO_SYM;
    }
    hasDerives &self -> bool { return self.deriveBy.len() > 0; }

    // ─── aliases ─────────────────────────────────────────────────────────────

    addAlias &self a:AliasDef -> void {
        self.aliases.push(a);
        self.aliasAt.put(nameOf(a.name), self.aliases.len() - 1);
    }
    // ─── generic templates ───────────────────────────────────────────────────

    addTemplate &self t:GTemplate -> void {
        self.templates.push(t);
        self.templateAt.put(t.name as long, self.templates.len() - 1);
    }
    findTemplate &self q:str -> long { return self.findTemplateSym(symIfAny(q)); }
    findTemplateSym &self n:Sym -> long {
        hit: Option<long> = self.templateAt.find(n as long);
        match hit { Some(i) { return i; } None { } }
        return NOT_FOUND;
    }
    isGeneric &self q:str -> bool { return self.findTemplate(q) >= 0; }
    isGenericSym &self n:Sym -> bool { return self.findTemplateSym(n) >= 0; }

    // The template an instance name was stamped from: `Option_long` -> `Option`. An instance is
    // not a type at parse time, and a generic use written inside a template is a pattern that is
    // never requested, so neither table answers for it; the mangled name still spells its base.
    // Longest match wins, so `Vec_Pair` finds `Vec` and not a `V` that happens to exist.
    templateOfInstance &self inst:str -> long {
        best: long = NOT_FOUND;
        bestLen: long = 0;
        for i in 0..self.templates.len() {
            n: str = nameOf(self.templates.get(i).name);
            if (n.len < inst.len && n.len > bestLen
                && charAt(inst, n.len) == '_' && strStartsWith(inst, n)) {
                best = i;
                bestLen = n.len;
            }
        }
        return best;
    }

    // What monomorphization reads back out: the template, its parameter names, its fields, and
    // the queue of instances the program asked for. All of it is stored as runs, so every one of
    // these is an index into the flat vector the template points into.
    templateDef &self i:long -> GTemplate { return self.templates.get(i); }
    gParamAt &self t:GTemplate k:long -> Sym { return self.gParams.get(t.firstParam + k); }
    gParamIsLen &self t:GTemplate k:long -> bool { return self.gParamInfo.get(t.firstParam + k).isLen; }
    // What the parameter is when a use leaves it out; `Lit.Void` if it has to be given.
    gParamDefault &self t:GTemplate k:long -> TypeRef { return self.gParamInfo.get(t.firstParam + k).deflt; }
    // Which parameter `name` is, or -1.
    gParamIndex &self t:GTemplate name:Sym -> long {
        for k in 0..t.paramCount {
            if (self.gParamAt(t, k) == name) { return k; }
        }
        return NOT_FOUND;
    }
    // The parameters of a template, appended as one run; returns where the run starts. Names and
    // kinds go in together so the two tables cannot drift apart.
    addGParams &self names:Vec<Sym> infos:Vec<GParamInfo> -> long {
        first: long = self.gParams.len();
        self.gParams.extend(names);
        self.gParamInfo.extend(infos);
        return first;
    }
    gFieldAt &self t:GTemplate k:long -> GField { return self.gFields.get(t.firstField + k); }
    gVariantAt &self t:GTemplate k:long -> GVariant { return self.gVariants.get(t.firstVariant + k); }
    addGVariants &self vs:Vec<GVariant> -> long {
        first: long = self.gVariants.len();
        self.gVariants.extend(vs);
        return first;
    }
    // Which variant of a generic sum type `name` is, or -1.
    findGVariant &self t:GTemplate name:str -> long {
        for k in 0..t.variantCount {
            if (nameOf(self.gVariantAt(t, k).name) == name) { return k; }
        }
        return NOT_FOUND;
    }

    addBounds &self bs:Vec<MethodBound> -> long {
        first: long = self.bounds.len();
        self.bounds.extend(bs);
        return first;
    }
    boundAt &self i:long -> MethodBound { return self.bounds.get(i); }

    // Type arguments parked for a request that is not a struct instantiation: a generic
    // function's, which a call infers and monomorphization reads back.
    addGenericArgs &self args:Vec<TypeRef> -> long {
        first: long = self.gArgs.len();
        self.gArgs.extend(args);
        return first;
    }
    genericArgAt &self first:long k:long -> TypeRef { return self.gArgs.get(first + k); }

    requestCount &self -> long { return self.requests.len(); }
    // A request is a pattern (a use written inside a template, not a type to stamp) when any of
    // its arguments still stands for a parameter. `Mutex<T>` written inside a template asks for
    // an instance whose argument is still a parameter; it names a pattern, not a type, and only
    // becomes a real request once an enclosing stamp binds it.
    //
    // An argument stands for a parameter when it is a type variable, or an instance of another
    // template that is itself a pattern. Looking one level deep is not enough: `Wrap<Wrap<A>>`
    // records its argument as the instance name `Wrap_A`, a Struct and not a TypeVar. Taken as a
    // concrete type it would be stamped, `substInstance` would decline to rebuild it, and the
    // stamped method would come back returning `Wrap_Wrap_A`, a struct whose own field has no
    // size.
    isPatternRequest &self r:GRequest -> bool { return self.patternArg(r, 0); }

    patternArg &self r:GRequest depth:long -> bool {
        if (depth > 32) { return false; }
        for k in 0..r.argCount {
            if (self.patternType(self.gArgAt(r, k), depth)) { return true; }
        }
        return false;
    }
    // A type that still names a parameter: `T`, an instance over one, or a tuple holding one.
    patternType &self t:TypeRef depth:long -> bool {
        if (t.base == Lit.TypeVar) { return true; }
        if (t.base != Lit.Struct || t.name == NO_SYM || depth > 32) { return false; }
        at: long = self.findRequestSym(t.name);
        if (at >= 0) { return self.patternArg(self.requests.get(at), depth + 1); }
        if (!isTupleName(t.name)) { return false; }
        si: long = self.findStructSym(t.name);
        if (si < 0) { return false; }
        d: StructDef = self.structs.get(si);
        for k in 0..d.fieldCount {
            f: FieldDef = self.fields.get(d.firstField + k);
            if (self.patternType(TypeRef { base: f.kind, name: f.structName }, depth + 1)) { return true; }
        }
        return false;
    }
    findRequest &self instance:str -> long { return self.findRequestSym(symIfAny(instance)); }
    findRequestSym &self instance:Sym -> long {
        hit: Option<long> = self.requestIx.find(instance as long);
        match hit { Some(i) { return i; } None { } }
        return NOT_FOUND;
    }
    requestAt &self i:long -> GRequest { return self.requests.get(i); }

    // `n` (a struct, or a generic one) holds a closure's captures. Marked before any instance of
    // it is requested, so `request` can pass the mark on.
    markClosure &self n:Sym -> void {
        if (self.journal && !self.closureEnvs.has(n as long)) { self.noteAdded(KEY_CLOSURE, n); }
        self.closureEnvs.put(n as long, true);
    }
    isClosureEnv &self n:Sym -> bool { return n != NO_SYM && self.closureEnvs.has(n as long); }
    requestPos &self i:long -> long { return self.reqPos.get(i); }
    gArgAt &self r:GRequest k:long -> TypeRef { return self.gArgs.get(r.firstArg + k); }

    // Ask for `base<args>` to be stamped out. Duplicates are harmless (monomorphization keys on
    // the instance name) but they are cheap to skip here.
    //
    // In a package build, a type a dependency's function BODY names is asked for, but held back
    // (`deferIn`): that body is not checked here, so nothing here needs the instance, and
    // stamping one clones and checks every method it has. It is released the moment anything
    // else asks for it, or when a body of that module is checked after all (`releaseModule`).
    request &self base:Sym instance:Sym args:Vec<TypeRef> -> void {
        hit: Option<long> = self.requestIx.find(instance as long);
        match hit {
            Some(i) {
                if (self.deferIn != NO_SYM) { self.noteDeferred(i); }
                else if (self.reqDeferred.get(i)) { self.release(i); }
                return;
            }
            None { }
        }
        first: long = self.gArgs.len();
        self.gArgs.extend(args);
        self.requests.push(GRequest { base: base, instance: instance,
                                      firstArg: first, argCount: args.len() });
        self.requestIx.put(instance as long, self.requests.len() - 1);
        if (self.closureEnvs.has(base as long)) { self.markClosure(instance); }
        self.reqDeferred.push(self.deferIn != NO_SYM);
        self.reqPos.push(gPos);
        noteOrigin(instance, gPos, NO_SYM);
        if (self.deferIn != NO_SYM) { self.noteDeferred(self.requests.len() - 1); }
    }

    // Held back on behalf of the module being read; chained per module.
    noteDeferred &self i:long -> void {
        key: str = nameOf(self.deferIn);
        prev: long = -1;
        hit: Option<long> = self.deferHead.find(key);
        match hit { Some(h) { prev = h; } None { } }
        self.deferReq.push(i);
        self.deferNext.push(prev);
        self.deferHead.put(key, self.deferReq.len() - 1);
    }
    release &self i:long -> void {
        if (!self.reqDeferred.get(i)) { return; }
        self.reqDeferred.set(i, false);
        self.released.push(i);
    }
    // Releases every instance a body of `module` named, because a function there is about to be
    // checked. Returns whether that left anything for monomorphization to stamp first.
    releaseModule &self module:Sym -> bool {
        key: str = nameOf(module);
        hit: Option<long> = self.deferHead.find(key);
        d: long = -1;
        match hit { Some(h) { d = h; } None { return self.released.len() > 0; } }
        self.deferHead.remove(key);
        while (d >= 0) { self.release(self.deferReq.get(d)); d = self.deferNext.get(d); }
        return self.released.len() > 0;
    }
    isDeferred &self i:long -> bool { return self.reqDeferred.get(i); }
    // The requests released since monomorphization last looked, handed over and forgotten.
    takeReleased &self -> Vec<long> {
        out: Vec<long>;
        out.extend(self.released);
        self.released.clear();
        return out;
    }
    hasReleased &self -> bool { return self.released.len() > 0; }

    // The qualified name of a type spelled bare. A name belongs to the module that declared it,
    // so `File` written in module `io` means `file::File`, the declaring module, not the using
    // one.
    //
    // The current module answers first, because a declaration made here shadows one imported from
    // elsewhere. Then the module's import closure, which the scanner publishes as `gImports`: only
    // a module this one can actually reach may answer, and two reachable modules declaring the
    // name is not a tie to be broken by whichever registered first. It is ambiguous, and the
    // caller has to say which.
    //
    // The last step is a search for any declaration anywhere whose last component matches. It
    // stays as the fallback because the import graph cannot answer for everything: a single-file
    // program has no edges at all, and a name the compiler itself reaches for is not written in
    // anyone's source.
    //
    // `rival` is the other declaration of the name, when two reachable modules declare it. It is
    // handed back rather than reported here because the parser knows where the name was written
    // and this table does not, and a diagnostic that points at a line is worth much more than one
    // that cannot.
    resolveBareIn &self here:str bare:str -> BareName {
        // Already qualified: `write::BufWriterConfig` names the module it comes from, so there is
        // nothing to resolve. Qualifying it again would ask for `here::write::BufWriterConfig`,
        // which nothing declares, and the last-component index is keyed on `BufWriterConfig`
        // alone, so it would not answer either. The name would fall through as undeclared, and a
        // variant written on it (`write::BufWriterConfig.LineBuffered`) would read as a field
        // access on nothing.
        if (lastComponentOf(bare).len != bare.len && self.declares(bare)) {
            return BareName { name: intern(bare), rival: NO_SYM };
        }
        own: Sym = qualifiedName(here, bare);
        if (self.declares(nameOf(own))) { return BareName { name: own, rival: NO_SYM }; }

        if (!gImports.isEmpty()) {
            self.indexLastComponents();
            found: Sym = NO_SYM;
            rival: Sym = NO_SYM;
            i: long = self.byBare.firstOf(bare);
            while (i >= 0) {
                cand: Sym = self.byBare.qualAt(i);
                own: Sym = self.byBare.ownerAt(i);
                i = self.byBare.nextOf(i);
                if (own == NO_SYM || !gImports.reaches(here, own)) { continue; }
                if (found != NO_SYM && found != cand && rival == NO_SYM) { rival = cand; }
                if (found == NO_SYM) { found = cand; }
            }
            if (found != NO_SYM) { return BareName { name: found, rival: rival }; }
        }
        // A `pub` trait's name is flat: it is its own spelling, wherever it is written. Asked
        // before the last-component fallback below, which could otherwise answer with another
        // file's own trait of the same spelling.
        if (self.findTrait(bare) >= 0) { return BareName { name: intern(bare), rival: NO_SYM }; }

        // `ast` is visible from everywhere: a macro is written against its `Node`, and the
        // module declaring the macro may sit below `ast` in the include order (`vec`).
        pre: Sym = qualifiedName("ast", bare);
        if (self.declares(nameOf(pre))) { return BareName { name: pre, rival: NO_SYM }; }

        hit: Sym = self.endsWithName(bare);
        if (hit != NO_SYM) { return BareName { name: hit, rival: NO_SYM }; }
        return BareName { name: own, rival: NO_SYM };
    }

    // The same, for a caller with no position to report from. An ambiguity here is still an
    // error, just one that cannot say where.
    resolveBare &self here:str bare:str -> Sym {
        b: BareName = self.resolveBareIn(here, bare);
        if (b.rival != NO_SYM) { failStr(ambiguousName(bare, b)); }
        return b.name;
    }

    // Is `q` a declared type name: a struct, an enum, a template, an alias or a trait? The five
    // tables a bare type name can resolve into, each an indexed lookup.
    declares &self q:str -> bool {
        return self.hasStruct(q) || self.findEnum(q) >= 0 || self.findTemplate(q) >= 0
            || self.findAlias(q) >= 0 || self.findTrait(q) >= 0;
    }

    // Any declared name whose last component is `bare`. There is one index per table, consulted
    // in a fixed precedence (a struct, then an enum, a template, a trait, an alias, whenever each
    // was declared), because a single index would order by arrival instead, and a struct
    // declared after a template of the same name would lose.
    //
    // The enum table is asked right after the struct one, matching the earlier C++ compiler,
    // which took structs and enums together before falling through to traits and aliases.
    // Without the enum table, an enum declared in another module would not be found, and
    // `BufWriterConfig.LineBuffered` written in `io` would read as a field access on a struct
    // nobody declared rather than as the constant it is.
    endsWithName &self bare:str -> Sym {
        self.indexLastComponents();
        n: Sym = lastHit(&self.byStructLast, bare);
        if (n != NO_SYM) { return n; }
        n = lastHit(&self.byEnumLast, bare);
        if (n != NO_SYM) { return n; }
        n = lastHit(&self.byTemplateLast, bare);
        if (n != NO_SYM) { return n; }
        n = lastHit(&self.byTraitLast, bare);
        if (n != NO_SYM) { return n; }
        return lastHit(&self.byAliasLast, bare);
    }
    // Brings each index up to date with its table. Each remembers how far it was indexed, so a
    // declaration is looked at once however often this is called, and the first declaration of a
    // name wins.
    indexLastComponents &self -> void {
        while (self.lastStructs < self.structs.len()) {
            noteLast(&self.byStructLast, self.structs.get(self.lastStructs).name);
            self.byBare.add(self.structs.get(self.lastStructs).name);
            self.lastStructs = self.lastStructs + 1;
        }
        while (self.lastEnums < self.enums.len()) {
            noteLast(&self.byEnumLast, self.enums.get(self.lastEnums).name);
            self.byBare.add(self.enums.get(self.lastEnums).name);
            self.lastEnums = self.lastEnums + 1;
        }
        while (self.lastTemplates < self.templates.len()) {
            noteLast(&self.byTemplateLast, self.templates.get(self.lastTemplates).name);
            self.byBare.add(self.templates.get(self.lastTemplates).name);
            self.lastTemplates = self.lastTemplates + 1;
        }
        while (self.lastTraits < self.traits.len()) {
            noteLast(&self.byTraitLast, self.traits.get(self.lastTraits).name);
            self.byBare.add(self.traits.get(self.lastTraits).name);
            self.lastTraits = self.lastTraits + 1;
        }
        while (self.lastAliases < self.aliases.len()) {
            noteLast(&self.byAliasLast, self.aliases.get(self.lastAliases).name);
            self.byBare.add(self.aliases.get(self.lastAliases).name);
            self.lastAliases = self.lastAliases + 1;
        }
    }

    findAlias &self q:str -> long {
        hit: Option<long> = self.aliasAt.find(q);
        match hit { Some(i) { return i; } None { } }
        return NOT_FOUND;
    }
    aliasDef &self i:long -> AliasDef { return self.aliases.get(i); }

    // A `pub` alias of this bare name declared somewhere other than `mine`. A `pub` name lives in
    // one flat cross-module namespace, so two of them are a collision whichever modules they were
    // written in; a private one is a name of its own file and collides with nothing. Linear: a
    // program has tens of aliases, and this is asked once per alias declared.
    otherPubAlias &self bare:str mine:Sym -> Sym {
        for i in 0..self.aliases.len() {
            d: AliasDef = self.aliases.get(i);
            if (d.visibility != Vis.Pub || d.name == mine) { continue; }
            if (lastComponentOf(nameOf(d.name)) == bare) { return d.name; }
        }
        return NO_SYM;
    }
}

// ─── taking a declaration back ───────────────────────────────────────────────
// The parser reads each top-level declaration under a `recover` (`Parser.parseDeclRecovering`),
// and one that an error cut short must leave nothing behind for the rest of the parse. Every
// table here is cut back to its length when the declaration began, and every key that pointed
// at what was cut goes with it. Declarations do not nest, so what lies past the mark is exactly
// what the declaration added.

pub struct RegMark {
    structs: long, fields: long, enums: long, variants: long, payloads: long,
    traits: long, traitMethods: long, traitArgs: long, impls: long, implFns: long,
    ownedTraits: long, traitInsts: long, globals: long, globalOrder: long, aliases: long,
    bare: long, lastStructs: long, lastEnums: long, lastTemplates: long, lastTraits: long,
    lastAliases: long, templates: long, gVariants: long, bounds: long, gParams: long,
    gFields: long, requests: long, gArgs: long, deferReq: long, released: long,
    deferIn: Sym, added: long, inProgress: long, sigs: long, sigParams: long, coreBuilt: bool
}

// A first-declaration index entry is put only for a name it lacks, so one naming `n` that was
// indexed since the mark was put since the mark.
local forgetLast inout m:HashMap<str, Sym> n:Sym -> void {
    key: str = lastComponentOf(nameOf(n));
    hit: Option<Sym> = m.find(key);
    match hit { Some(x) { if (x == n) { m.remove(key); } } None { } }
}
// An entry of a by-name table that points at `i`, which is being cut.
local forgetAt inout m:HashMap<str, long> key:str i:long -> void {
    hit: Option<long> = m.find(key);
    match hit { Some(x) { if (x == i) { m.remove(key); } } None { } }
}
local forgetAtNum inout m:HashMap<long, long> key:long i:long -> void {
    hit: Option<long> = m.find(key);
    match hit { Some(x) { if (x == i) { m.remove(key); } } None { } }
}

methods Registry {
    noteAdded &self tag:long n:Sym -> void { self.added.push(tag); self.added.push(n as long); }

    mark &self -> RegMark {
        return RegMark { structs: self.structs.len(), fields: self.fields.len(), enums: self.enums.len(),
                         variants: self.variants.len(), payloads: self.payloads.len(),
                         traits: self.traits.len(), traitMethods: self.traitMethods.len(),
                         traitArgs: self.traitArgs.len(), impls: self.impls.len(), implFns: self.implFns.len(),
                         ownedTraits: self.ownedTraits.len(), traitInsts: self.traitInsts.len(),
                         globals: self.globals.len(), globalOrder: self.globalOrder.len(),
                         aliases: self.aliases.len(), bare: self.byBare.qual.len(),
                         lastStructs: self.lastStructs, lastEnums: self.lastEnums,
                         lastTemplates: self.lastTemplates, lastTraits: self.lastTraits,
                         lastAliases: self.lastAliases, templates: self.templates.len(),
                         gVariants: self.gVariants.len(), bounds: self.bounds.len(),
                         gParams: self.gParams.len(), gFields: self.gFields.len(),
                         requests: self.requests.len(), gArgs: self.gArgs.len(),
                         deferReq: self.deferReq.len(), released: self.released.len(),
                         deferIn: self.deferIn, added: self.added.len(),
                         inProgress: gTypesInProgress.len(), sigs: gFnSigs.sigs.len(),
                         sigParams: gFnSigs.params.len(), coreBuilt: gCoreMethodsBuilt };
    }

    rewindTo &self m:RegMark -> void {
        // The bare-name index, newest entry first: each made itself the head of its name's chain,
        // in front of the one its `next` holds.
        b: long = self.byBare.qual.len();
        while (b > m.bare) {
            b = b - 1;
            key: str = lastComponentOf(nameOf(self.byBare.qual.get(b)));
            prev: long = self.byBare.next.get(b);
            if (prev >= 0) { self.byBare.head.put(key, prev); } else { self.byBare.head.remove(key); }
        }
        self.byBare.qual.truncate(m.bare);
        self.byBare.owner.truncate(m.bare);
        self.byBare.next.truncate(m.bare);
        // The first-declaration indexes lose what was indexed since the mark, and index it again
        // when next asked, from the tables as they will be.
        for k in m.lastStructs..self.lastStructs { forgetLast(&self.byStructLast, self.structs.get(k).name); }
        for k in m.lastEnums..self.lastEnums { forgetLast(&self.byEnumLast, self.enums.get(k).name); }
        for k in m.lastTemplates..self.lastTemplates { forgetLast(&self.byTemplateLast, self.templates.get(k).name); }
        for k in m.lastTraits..self.lastTraits { forgetLast(&self.byTraitLast, self.traits.get(k).name); }
        for k in m.lastAliases..self.lastAliases { forgetLast(&self.byAliasLast, self.aliases.get(k).name); }
        self.lastStructs = m.lastStructs;
        self.lastEnums = m.lastEnums;
        self.lastTemplates = m.lastTemplates;
        self.lastTraits = m.lastTraits;
        self.lastAliases = m.lastAliases;

        // Requests, with where each was asked for. One made before the mark that the declaration
        // released is held back again, and a chain of held-back requests that grew falls back to
        // the entry it was put in front of.
        for k in m.requests..self.requests.len() {
            inst: Sym = self.requests.get(k).instance;
            self.requestIx.remove(inst as long);
            forgetOrigin(inst);
        }
        for k in m.released..self.released.len() {
            r: long = self.released.get(k);
            if (r < m.requests) { self.reqDeferred.set(r, true); }
        }
        if (self.deferReq.len() > m.deferReq) {
            heads: Vec<str>;
            h: long = self.deferHead.nextSlot(-1);
            while (h >= 0) {
                if (self.deferHead.valAt(h) >= m.deferReq) { heads.push(self.deferHead.keyAt(h)); }
                h = self.deferHead.nextSlot(h);
            }
            for key in heads {
                d: long = self.deferHead.get(key);
                while (d >= m.deferReq) { d = self.deferNext.get(d); }
                if (d >= 0) { self.deferHead.put(key, d); } else { self.deferHead.remove(key); }
            }
        }

        // The by-name tables of everything else that is cut.
        for k in m.structs..self.structs.len() {
            d: StructDef = self.structs.get(k);
            forgetAt(&self.structAt, nameOf(d.name), k);
            forgetAtNum(&self.structAtSym, d.name as long, k);
            for f in 0..d.fieldCount {
                self.fieldAt2.remove(fieldKey(d.firstField, self.fields.get(d.firstField + f).name));
            }
        }
        for k in m.enums..self.enums.len() {
            n: Sym = self.enums.get(k).name;
            forgetAt(&self.enumAt, nameOf(n), k);
            forgetAtNum(&self.enumAtSym, n as long, k);
        }
        for k in m.traits..self.traits.len() {
            n: Sym = self.traits.get(k).name;
            forgetAtNum(&self.traitAt, n as long, k);
            hit: Option<long> = self.traitInstAt.find(n as long);
            match hit { Some(x) { if (x >= m.traitInsts) { self.traitInstAt.remove(n as long); } } None { } }
        }
        // An implementation that headed its (type, trait) chain goes with its key; one chained
        // behind an older one is unhooked from it.
        for k in m.impls..self.impls.len() {
            im: TraitImplDef = self.impls.get(k);
            forgetAtNum(&self.implAt2, implKey(im.structName, im.trait.name), k);
            if (im.carried) { forgetAt(&self.carriedOwners, nameOf(im.structName), k); }
        }
        if (self.impls.len() > m.impls) {
            for k in 0..m.impls {
                if (self.implNext.get(k) >= m.impls) { self.implNext.set(k, NOT_FOUND); }
                if (self.carriedNext.get(k) >= m.impls) { self.carriedNext.set(k, NOT_FOUND); }
            }
        }
        for k in m.globals..self.globals.len() { forgetAtNum(&self.globalAt, self.globals.get(k).name as long, k); }
        for k in m.aliases..self.aliases.len() { forgetAt(&self.aliasAt, nameOf(self.aliases.get(k).name), k); }
        for k in m.templates..self.templates.len() { forgetAtNum(&self.templateAt, self.templates.get(k).name as long, k); }
        // The sets that hold no index, by what the journal says they gained, newest first.
        a: long = self.added.len();
        while (a > m.added) {
            a = a - 2;
            tag: long = self.added.get(a);
            n: Sym = self.added.get(a + 1) as Sym;
            if (tag == KEY_MACRO) { self.macroAt.remove(nameOf(n)); }
            else if (tag == KEY_DERIVE) { self.deriveBy.remove(nameOf(n)); self.deriveIn.remove(nameOf(n)); }
            else if (tag == KEY_DISTINCT) { self.distinctBase.remove(nameOf(n)); }
            else if (tag == KEY_CLOSURE) { self.closureEnvs.remove(n as long); }
            else if (tag == KEY_IMPLFN) { self.implFnSet.remove(nameOf(n)); }
        }

        self.structs.truncate(m.structs);
        self.fields.truncate(m.fields);
        self.enums.truncate(m.enums);
        self.variants.truncate(m.variants);
        self.payloads.truncate(m.payloads);
        self.traits.truncate(m.traits);
        self.traitMethods.truncate(m.traitMethods);
        self.traitArgs.truncate(m.traitArgs);
        self.impls.truncate(m.impls);
        self.implFns.truncate(m.implFns);
        self.implNext.truncate(m.impls);
        self.carriedNext.truncate(m.impls);
        self.ownedTraits.truncate(m.ownedTraits);
        self.traitInsts.truncate(m.traitInsts);
        self.globals.truncate(m.globals);
        self.globalOrder.truncate(m.globalOrder);
        self.aliases.truncate(m.aliases);
        self.templates.truncate(m.templates);
        self.gVariants.truncate(m.gVariants);
        self.bounds.truncate(m.bounds);
        self.gParams.truncate(m.gParams);
        self.gParamInfo.truncate(m.gParams);
        self.gFields.truncate(m.gFields);
        self.requests.truncate(m.requests);
        self.reqDeferred.truncate(m.requests);
        self.reqPos.truncate(m.requests);
        self.gArgs.truncate(m.gArgs);
        self.deferReq.truncate(m.deferReq);
        self.deferNext.truncate(m.deferReq);
        self.released.truncate(m.released);
        self.added.truncate(m.added);
        self.deferIn = m.deferIn;
        gTypesInProgress.truncate(m.inProgress);
        gFnSigs.rewindTo(m.sigs, m.sigParams);
        // Built from the core traits: asked first during the declaration, it may hold what was cut.
        if (!m.coreBuilt && gCoreMethodsBuilt) { gCoreMethods.clear(); gCoreMethodsBuilt = false; }
    }
}

// One registry for the whole compile, for the same reason the interner is one: every phase reads
// it, and threading it through every signature would buy nothing.
pub var gReg: Registry;

// The table for one implementation. Named after the trait's instantiation, not just its name:
// `String` implements `Eq<str>` and `Eq<String>`, and those are two tables.
pub implVtableName im:TraitImplDef -> str {
    return vtableName(im.structName, intern(gReg.traitMangled(im.trait)));
}

// What one impl's method is called. A parameterized trait can be implemented several times for
// the same type, so its methods carry the instantiation; an unparameterized one cannot, and keeps
// the plain `Owner_method`.
pub implMethodName im:TraitImplDef method:Sym -> Sym {
    return implFnNameAs(im.structName, im.trait, method, im.carried);
}

// The same, for an implementation of `tr` by `owner` before it is registered. A trait a module
// owns (declared without `pub`, so `geo::Shape`) puts its name into its methods' names too.
// Another module's trait of the same spelling is a different trait, and both may be implemented
// for one type (a program's own `methods long for Ord` beside the standard library's), so without
// the trait's name `long_cmp` would be defined twice. A flat (`pub`) trait without arguments
// keeps `Owner_method`.
pub implFnName owner:Sym tr:TraitRef method:Sym -> Sym {
    return implFnNameAs(owner, tr, method, gReg.flatCarries(owner, tr));
}
// The same, with the flat trait's choice already made (`carried`; see `Registry.flatCarries`).
pub implFnNameAs owner:Sym tr:TraitRef method:Sym carried:bool -> Sym { return gReg.implFnNameIn(owner, tr, method, carried); }
pub traitCarriesName tr:TraitRef -> bool { return gReg.carriesName(tr); }
// A trait some module owns: declared without `pub`, so registered as `module::Name`.
pub isModuleTrait t:Sym -> bool { return gReg.moduleTrait(t); }

// The same questions asked of a registry rather than of `gReg`, which is how its own methods ask
// them: a method holding the registry lent `inout` may not name `gReg`, and one holding it lent to
// read may reach nothing that writes it by name.
methods Registry {
    implFnNameIn &self owner:Sym tr:TraitRef method:Sym carried:bool -> Sym {
        if (!carried && !self.carriesName(tr)) { return methodName(owner, method); }
        return methodName(methodName(owner, intern(self.traitMangled(tr))), method);
    }
    carriesName &self tr:TraitRef -> bool { return tr.argCount > 0 || self.moduleTrait(tr.name); }
    moduleTrait &self t:Sym -> bool {
        if (t == NO_SYM) { return false; }
        inst: long = self.traitInstOf(t);
        if (inst >= 0) { return self.moduleTrait(self.traitInstRef(inst).name); }
        return lastComponentOf(nameOf(t)).len != nameOf(t).len;
    }
}

// The traits the compiler wires into the language by name (`stdlib::core`'s, and the `FnN` it
// makes itself). They are one program-wide name each: a file that writes `trait Drop { ... }`
// re-declares core's rather than declaring a trait of its own, whatever its visibility.
pub isCoreTraitName s:str -> bool {
    if (strStartsWith(s, "Fn") && s.len > 2) {
        for i in 2..s.len {
            c: long = charAt(s, i);
            if (c < '0' as long || c > '9' as long) { return false; }
        }
        return true;
    }
    return gCoreTraits.has(s);
}
local var gCoreMethods: HashMap<str, bool> = map![];
local var gCoreMethodsBuilt: bool = false;
gCoreTraits: HashMap<str, bool> = map!["Drop" => true, "Clone" => true, "Copy" => true,
    "MustUse" => true, "Default" => true, "Write" => true, "Read" => true, "Display" => true,
    "Eq" => true, "Add" => true, "Sub" => true, "Mul" => true, "Div" => true, "Rem" => true,
    "BitAnd" => true, "BitOr" => true, "BitXor" => true, "Shl" => true, "Shr" => true,
    "Not" => true, "Index" => true, "IndexSet" => true];

// ─── layout ──────────────────────────────────────────────────────────────────
// A field's offset is decided here rather than where a struct is parsed, because it is decided
// twice: once as the declaration is read, and again once monomorphization has stamped everything
// a field's type might name. A struct holding a generic instance has no size the first time.

pub alignUp x:long a:long -> long { return (x + a - 1) / a * a; }

// The integer a backed enum's values actually are, or `Lit.Void` when the type is not one.
//
// A backed enum keeps its own name all the way down: `kind: Tok` is a `Lit.Struct` companioned
// "Tok", and only `namedScalar` in codegen ever unwraps it, so every other consumer sees an
// aggregate where there is really a four-byte integer. Layout is the one consumer that cannot
// live with that. The struct registry has no row named "Tok", so the size would come back 0 and
// the next field would be placed on top of this one; that once put a lexer's `punct`, `cls` and
// `two` tables all at the same offset and made the second-generation compiler read a token kind
// of -1.
//
// A sum type is a different thing with the same keyword: it is a tagged union, registered as a
// struct under its own name, and answers there like any other aggregate.
pub backedEnumBacking k:Lit n:Sym -> Lit { return gReg.enumBackingIn(k, n); }

// How many bytes a value of this type occupies where it is stored: a field, an array element.
// A named aggregate answers with its registered size; everything else with its kind's. A struct
// nothing has registered yet answers 0, which is the honest answer at parse time and the reason
// the layout is done again once monomorphization has stamped every instance.
pub typeSizeOf k:Lit n:Sym -> long { return gReg.typeSizeIn(k, n); }

// The same two, asked of a registry: what its own layout methods call.
methods Registry {
    enumBackingIn &self k:Lit n:Sym -> Lit {
        if (k != Lit.Struct || n == NO_SYM) { return Lit.Void; }
        q: str = nameOf(n);
        i: long = self.findEnum(q);
        if (i < 0 || self.isSumType(q)) { return Lit.Void; }
        return self.enumDef(i).backing;
    }
    typeSizeIn &self k:Lit n:Sym -> long {
        b: Lit = self.enumBackingIn(k, n);
        if (b != Lit.Void) { return typeInfo(b).size; }
        // A tuple answers the same way: it is registered as a struct under a name built from its
        // element types, so it has a size like any other aggregate. Without this arm it would
        // answer the row's own 0, and every field placed after one would land on top of it.
        if ((k == Lit.Struct || k == Lit.Tuple) && n != NO_SYM) {
            if (k == Lit.Struct && gTypesInProgress.len() > 0 && gTypesInProgress.get(gTypesInProgress.len() - 1) == n) {
                failStr(format("recursive type `{}` has infinite size\nnote: `{}` holds itself directly\nhelp: hold it behind an indirection: `Box<{}>`, `*{}` or `Vec<{}>`",
                               nameOf(n), nameOf(n), nameOf(n), nameOf(n), nameOf(n)));
            }
            at: long = self.findStructSym(n);
            if (at < 0) { return 0; }
            return self.structDef(at).size;
        }
        return typeInfo(k).size;
    }
    // `placeField`, asked of a registry.
    placeFieldIn &self cursor:long f:FieldDef -> Placed {
        esz: long = self.typeSizeIn(f.kind, f.structName);
        align: long = esz;
        // Every aggregate here is built of eight-byte words, so eight is its alignment, but a
        // backed enum only spells like one, and aligns to the width of the integer it is.
        if (isAggregate(f.kind) && self.enumBackingIn(f.kind, f.structName) == Lit.Void) { align = 8; }
        if (align < 1) { align = 1; }
        at: long = alignUp(cursor, align);
        span: long = esz;
        if (f.isArray) { span = f.count * esz; }
        placed: FieldDef = f;
        placed.offset = at;
        return Placed { field: placed, next: at + span };
    }
}

// A named type that is nevertheless one register wide: an enum with no payloads, whose values are
// its backing integer. A sum type (an enum with payloads) is a tagged union and is laid out as
// an aggregate, so it is not one of these.
pub namedScalar k:Lit n:Sym -> bool {
    if (k != Lit.Struct || n == NO_SYM) { return false; }
    i: long = gReg.findEnumSym(n);
    return i >= 0 && !gReg.enumDef(i).hasPayload;
}

// The integer type such an enum's values actually are.
pub namedScalarBacking n:Sym -> Lit {
    i: long = gReg.findEnumSym(n);
    if (i < 0) { return Lit.Long; }
    return gReg.enumDef(i).backing;
}

// The type a value of this type is stored as. A backed enum keeps its own name all the way through
// the front end (`kind: Tok` is a `Lit.Struct` companioned "Tok"), so every question about width
// has to unwrap it first. What a field holds, what a load reads, what a store writes and what an
// array strides by is the backing integer, while `Lit.Struct` would answer with the eight bytes an
// unrecognised named type falls back to. Read as eight bytes, a `Tok` field comes back with the
// next field's value in its top half, and an eight-byte stride makes `[TokInfo; 47]` and the
// tables beside it disagree about where their rows are.
//
// Everything a value does in a register is unaffected (a temp is a register either way), so this
// belongs at the memory boundary and nowhere else.
pub storedKind k:Lit n:Sym -> Lit {
    if (k != Lit.Struct || n == NO_SYM) { return k; }
    i: long = gReg.findEnumSym(n);            // one lookup: `namedScalar`, then its backing
    if (i >= 0 && !gReg.enumDef(i).hasPayload) { return gReg.enumDef(i).backing; }
    return k;
}

// The byte size of a type, exactly, which is what `sizeof` answers and what a stride is computed
// from. Unlike `aggregateBytes` it does not round a narrow scalar up to a register: `sizeof(u8)`
// is 1, and a `*u8` walking by 8 reads every eighth byte of a string.
pub typeBytes k:Lit n:Sym -> long {
    // A backed enum is its backing integer, which is also the stride the struct registry laid its
    // array fields out with. Falling through to the eight-byte default for an unrecognised named
    // type would put every stride here at odds with every offset there.
    if (namedScalar(k, n)) { return typeInfo(namedScalarBacking(n)).size; }
    if (k == Lit.Struct || k == Lit.Tuple) {
        if (n != NO_SYM) {
            at: long = gReg.findStructSym(n);
            if (at >= 0) { return gReg.structDef(at).size; }
        }
        return 8;
    }
    b: long = typeInfo(k).size;
    if (b < 1) { return 8; }
    return b;
}

// How wide the type `n` names is: a struct asks the registry, anything else is a scalar spelling.
pub namedWidth n:Sym -> long {
    if (n == NO_SYM) { return 8; }
    if (namedScalar(Lit.Struct, n)) { return typeInfo(namedScalarBacking(n)).size; }
    at: long = gReg.findStructSym(n);
    if (at >= 0) { return gReg.structDef(at).size; }
    w: long = typeInfo(scalarNamed(lastComponentOf(nameOf(n)))).size;
    if (w < 1) { w = 8; }
    return w;
}

// The synthetic field names a sum type's layout uses. `$` cannot appear in an identifier, so none
// of these can be written in source: the tag and the payload are reachable only through a variant
// constructor and `match`, which is what keeps "exactly one variant is live" from being sidestepped
// by a field access.
pub enumTagField -> str { return "$tag"; }

pub enumPayloadField variant:str i:long -> Sym {
    s: String;
    s.push('$');
    s.pushStr(variant);
    s.push('$');
    s.pushLong(i);
    out: Sym = NO_SYM;
    out = internString(s);
    return out;
}

// A field as a message names it: "its field `f`", or, for a sum type's payload slot `$V$k`, the
// variant it carries.
pub cloneFieldLabel d:StructDef n:Sym -> str {
    s: str = nameOf(n);
    if (!d.isEnum || s.len < 2 || charAt(s, 0) != '$') { return keepString(format("its field `{}`", s)); }
    e: long = 1;
    while (e < s.len && charAt(s, e) != '$') { e = e + 1; }
    return keepString(format("the payload of its variant `{}`", strSlice(s, 1, e - 1)));
}

// `f` arrives with everything but its offset filled in. Taking it whole rather than as five
// separate arguments also keeps the call within the six the ABI has registers for: an aggregate
// return already spends one of them on its hidden destination pointer.
pub placeField cursor:long f:FieldDef -> Placed { return gReg.placeFieldIn(cursor, f); }

// ─── tuples ──────────────────────────────────────────────────────────────────
// A tuple is structural: `(int, int)` written in two files is one type, because nothing names it
// and the element types are all there is to go on. So it is registered as an ordinary struct
// under a name built from those element types, and every phase after this treats it as the
// aggregate it is. It has fields, offsets and a size like any other, and none of them has to
// learn what a tuple is. That is the same move `layoutEnum` makes for a sum type.
//
// The name cannot collide with anything written in source: `$` is not an identifier character,
// so `$tuple$int$int` is unwritable and the second `(int, int)` met finds the first's registration
// rather than making a rival one.

// The element's spelling inside a tuple's name is what `typeMangleName` answers for it, as in an
// instance's name. An element may itself be a tuple, so the name closes with a `$` of its own:
// `$tuple$$tuple$long$long$$long$` is `((long, long), long)` and `$tuple$$tuple$long$long$long$$`
// is `((long, long, long),)`, which without the closing mark would be the same text. It is what
// a `.klib` and every instance built over a tuple (`Vec_$tuple$long$long$`) are keyed by.
pub tupleTypeName elems:Vec<TypeRef> -> Sym {
    s: String;
    s.pushStr("$tuple");
    for i in 0..elems.len() {
        e: TypeRef = elems.get(i);
        s.push('$');
        s.pushStr(typeMangleName(e.base, e.name));
    }
    s.push('$');
    return internString(s);
}

// The element types of a registered tuple, read back from its fields.
pub tupleElems n:Sym -> Vec<TypeRef> {
    out: Vec<TypeRef>;
    at: long = gReg.findStructSym(n);
    if (at < 0) { return out; }
    d: StructDef = gReg.structDef(at);
    for k in 0..d.fieldCount {
        f: FieldDef = gReg.fieldAt(d, k);
        out.push(TypeRef { base: f.kind, name: f.structName });
    }
    return out;
}

// Is this the name of a tuple's k-th element (`$0`, `$1`, ...)? Distinct from a sum type's
// payload slot (`$Some$0`), the other field name nothing written in source can spell.
pub isTupleField n:Sym -> bool {
    if (n == NO_SYM) { return false; }
    s: str = nameOf(n);
    return s.len > 1 && charAt(s, 0) == '$' && isDigit(charAt(s, 1));
}

// The k-th element's field name. Positional, and unwritable for the same reason as the type name:
// a tuple's elements are reached by position, never by a name someone could have spelled.
pub tupleFieldName k:long -> Sym {
    s: String;
    s.push('$');
    s.pushLong(k);
    return internString(s);
}

// Registers `(A, B, ...)` and returns the struct name it is now known by. Idempotent: the same
// element list registers once and every later mention finds it.
//
// The layout is the natural one (each field aligned to its own width, the whole rounded to 8),
// which is exactly what `placeField` does for a declared struct, so a tuple and a struct with the
// same fields have the same shape and one code path lays out both.
pub registerTuple elems:Vec<TypeRef> -> Sym {
    name: Sym = tupleTypeName(elems);
    if (gReg.hasStructSym(name)) { return name; }
    fs: Vec<FieldDef>;
    cursor: long = 0;
    for i in 0..elems.len() {
        e: TypeRef = elems.get(i);
        p: Placed = placeField(cursor, FieldDef { name: tupleFieldName(i), kind: e.base,
                                                  structName: e.name, offset: 0,
                                                  isArray: false, count: 0 });
        fs.push(p.field);
        cursor = p.next;
    }
    gReg.addStruct(name, fs, alignUp(cursor, 8), false);
    return name;
}

// Is `n` a registered tuple rather than a struct someone declared? The name says so, and nothing
// written in source can claim it.
pub isTupleName n:Sym -> bool {
    if (n == NO_SYM) { return false; }
    return strStartsWith(nameOf(n), "$tuple");
}

// ─── function-pointer signatures ─────────────────────────────────────────────
//
// A `fn` type is not one type but a family, and what tells two members apart is the whole
// signature. `fn(Res)->long` lends its argument and `fn(sink Res)->long` takes it, so an
// indirect call through the second moves a value the first only borrows. Keyed by the return
// type alone, those two would be the same type, and the callee would release its parameter only
// for the caller to release it again.
//
// So a `Lit.Fn`'s companion name is a key (the canonical spelling of the signature) and this
// is the table it keys. Interning on that spelling means an identical signature met twice is one
// entry found by one hash, which matters: the table is asked at every fn-typed call and at every
// `&f`, and a scan there would be a scan in the hot path of every callback in the program.

// One parameter of a signature: its type, and how the call hands it over. It is a struct of its
// own rather than a `TypeRef` with a parallel array of conventions beside it, because two arrays
// that must stay the same length are easy to get wrong.
pub struct FnParam { kind: Lit, name: Sym, conv: Conv }

pub fnParamOf t:TypeRef c:Conv -> FnParam { return FnParam { kind: t.base, name: t.name, conv: c }; }
pub fnParamType p:FnParam -> TypeRef { return TypeRef { base: p.kind, name: p.name }; }

// The parameters are a run in one flat vector, the way every other variable-length part of a
// declaration is recorded here.
pub struct FnSig { firstParam: long, paramCount: long, ret: TypeRef }

pub struct FnSigTable {
    params: Vec<FnParam>,
    sigs:   Vec<FnSig>,
    at:     HashMap<str, long>
}

methods FnSigTable for Default {
    new -> FnSigTable {
        return FnSigTable { params: vec![], sigs: vec![], at: map![] };
    }
}

methods FnSigTable {
    // The canonical spelling of a signature, which is the key it interns under.
    //
    // A named type keys by its name, so `fn(long, Write)` and `fn(long, Display)` are not one
    // type. A consuming parameter keys by saying so, so `fn(sink T)` and `fn(T)` are not one
    // either. That is the whole point of the table. A borrow and the value it borrows spell the
    // same, because convention inference retypes a read struct parameter to the borrow
    // representation: `fn(&Res)` and `fn(Res)` are one contract written two ways.
    key &self ps:Vec<FnParam> ret:TypeRef -> String {
        s: String;
        s.pushStr("fn(");
        for i in 0..ps.len() {
            if (i > 0) { s.push(','); }
            p: FnParam = ps.get(i);
            if (p.conv == Conv.Sink) { s.pushStr("sink "); }
            if (p.name == NO_SYM) { s.pushStr(typeName(p.kind)); } else { s.pushStr(nameOf(p.name)); }
        }
        s.pushStr(")->");
        if (ret.base == Lit.Ref) { s.push('&'); }   // a borrow returned is not the value returned
        if (ret.name == NO_SYM) { s.pushStr(typeName(ret.base)); } else { s.pushStr(nameOf(ret.name)); }
        return s;
    }

    // Records a signature and returns its key: the companion name a `Lit.Fn` then carries.
    // Idempotent: the same signature met again finds the entry it already made.
    register &self ps:Vec<FnParam> ret:TypeRef -> Sym {
        spelling: String = self.key(ps, ret);
        k: Sym = internString(spelling);
        if (self.at.has(nameOf(k))) { return k; }
        first: long = self.params.len();
        self.params.extend(ps);
        self.sigs.push(FnSig { firstParam: first, paramCount: ps.len(), ret: ret });
        self.at.put(nameOf(k), self.sigs.len() - 1);
        return k;
    }

    find &self key:Sym -> long {
        if (key == NO_SYM) { return NOT_FOUND; }
        hit: Option<long> = self.at.find(nameOf(key));
        match hit { Some(i) { return i; } None { } }
        return NOT_FOUND;
    }

    // Back to `sigs` signatures and `params` parameters, for a declaration taken back
    // (`Registry.rewindTo`). A removed slot stays a tombstone, so a key can go mid-walk.
    rewindTo &self sigs:long params:long -> void {
        if (self.sigs.len() == sigs) { return; }
        i: long = self.at.nextSlot(-1);
        while (i >= 0) {
            if (self.at.valAt(i) >= sigs) {
                key: str = self.at.keyAt(i);
                self.at.remove(key);
            }
            i = self.at.nextSlot(i);
        }
        self.sigs.truncate(sigs);
        self.params.truncate(params);
    }

    sigAt &self i:long -> FnSig { return self.sigs.get(i); }
    paramAt &self s:FnSig k:long -> FnParam { return self.params.get(s.firstParam + k); }
}

// One table for the whole compile, for the same reason the registry and the interner are one.
pub var gFnSigs: FnSigTable;

// Do two fn types describe the same shape (same arity, same result, same parameter types)
// setting aside how each parameter is handed over?
local fnSigsSameShape x:FnSig y:FnSig -> bool {
    if (x.paramCount != y.paramCount) { return false; }
    if (x.ret != y.ret) { return false; }
    for k in 0..x.paramCount {
        p: FnParam = gFnSigs.paramAt(x, k);
        q: FnParam = gFnSigs.paramAt(y, k);
        if (p.kind != q.kind || p.name != q.name) { return false; }
    }
    return true;
}

// Does some parameter say `sink` in one signature and not in the other, for a type that owns
// something? That is the one difference between two fn types of the same shape that cannot be
// papered over: through the first the caller keeps the value and through the second it gives it
// up, so whichever way round it is, one end releases what the other already released.
local fnSigsOwnershipClash x:FnSig y:FnSig -> bool {
    for k in 0..x.paramCount {
        p: FnParam = gFnSigs.paramAt(x, k);
        q: FnParam = gFnSigs.paramAt(y, k);
        if ((p.conv == Conv.Sink) != (q.conv == Conv.Sink) && gReg.needsDrop(p.name)) { return true; }
    }
    return false;
}

// Two fn types of the same shape, disagreeing where it matters. Asked this way round rather than
// "do these two match", because a general fn-type mismatch is somebody else's diagnosis: what is
// reported here is only the case whose whole content is who releases the argument. Two that
// differ solely in a `sink` on a parameter owning nothing are the same contract (consuming and
// borrowing a value with no release are the same thing with or without a copy) so any callee of
// that shape fits any pointer of it, and this answers false for them.
pub fnSigsClashOnOwnership a:Sym b:Sym -> bool {
    ia: long = gFnSigs.find(a);
    ib: long = gFnSigs.find(b);
    if (ia < 0 || ib < 0) { return false; }
    x: FnSig = gFnSigs.sigAt(ia);
    y: FnSig = gFnSigs.sigAt(ib);
    if (!fnSigsSameShape(x, y)) { return false; }
    return fnSigsOwnershipClash(x, y);
}

// One parameter type of a fn signature against another: the same type, a struct and a borrow of
// it alike (convention inference retypes a read parameter to the borrow, and the key spells the
// two the same), a fn type by `fnSigsFit`. A type parameter is a pattern and fits anything: the
// stamped instance is what is held to it.
local fnTypesFit pk:Lit pn:Sym qk:Lit qn:Sym -> bool {
    if (pk == Lit.TypeVar || qk == Lit.TypeVar) { return true; }
    if (pk == Lit.Fn && qk == Lit.Fn) { return fnSigsFit(pn, qn); }
    if (pn != qn) { return false; }
    if (pk == qk) { return true; }
    return (pk == Lit.Ref || pk == Lit.Struct) && (qk == Lit.Ref || qk == Lit.Struct);
}

// Whether a fn value typed `got` may stand where a `want` is. A call through it is compiled
// against `want`, so the function it holds must take the same arguments the same way and give
// back the same result: the same arity, the same parameter and result types, and the same word
// (lend or `sink`) on every parameter whose type owns something, since through one the caller
// keeps the value and through the other it gives it up. A `sink` on a parameter that owns
// nothing changes only whether the callee copies (its prologue does), so either fits either
// there. Without this check, `f: fn(long)->long = &look` with `look r:Res` would read the
// integer as an address.
pub fnSigsFit want:Sym got:Sym -> bool {
    if (want == got) { return true; }
    ia: long = gFnSigs.find(want);
    ib: long = gFnSigs.find(got);
    if (ia < 0 || ib < 0) { return true; }      // no signature to hold it to: not this question
    x: FnSig = gFnSigs.sigAt(ia);
    y: FnSig = gFnSigs.sigAt(ib);
    if (x.paramCount != y.paramCount) { return false; }
    if (!fnTypesFit(x.ret.base, x.ret.name, y.ret.base, y.ret.name)) { return false; }
    if ((x.ret.base == Lit.Ref) != (y.ret.base == Lit.Ref)) { return false; }   // a borrow is not the value
    for k in 0..x.paramCount {
        p: FnParam = gFnSigs.paramAt(x, k);
        q: FnParam = gFnSigs.paramAt(y, k);
        if (!fnTypesFit(p.kind, p.name, q.kind, q.name)) { return false; }
    }
    return !fnSigsOwnershipClash(x, y);
}

// ─── in a `.klib` ────────────────────────────────────────────────────────────
// A field carries a length, which inside a template may still name its parameter (`putCount`),
// so these two codecs are written out rather than derived.
methods GField for Encode {
    encode &self out:&Encoder -> void {
        self.name.encode(out); self.kind.encode(out); self.isArray.encode(out); putCount(out, self.count);
    }
}
methods GField for Decode {
    decode inp:&Decoder -> GField {
        name: Sym = Sym.decode(inp);
        kind: TypeRef = TypeRef.decode(inp);
        isArray: bool = bool.decode(inp);
        return GField { name: name, kind: kind, isArray: isArray, count: getCount(inp) };
    }
}
methods FieldDef for Encode {
    encode &self out:&Encoder -> void {
        self.name.encode(out); self.kind.encode(out); self.structName.encode(out);
        out.putVarint(self.offset); self.isArray.encode(out); putCount(out, self.count);
    }
}
methods FieldDef for Decode {
    decode inp:&Decoder -> FieldDef {
        name: Sym = Sym.decode(inp);
        kind: Lit = Lit.decode(inp);
        sn: Sym = Sym.decode(inp);
        offset: long = inp.getVarint();
        isArray: bool = bool.decode(inp);
        return FieldDef { name: name, kind: kind, structName: sn, offset: offset, isArray: isArray,
                          count: getCount(inp) };
    }
}

// `Drop`'s name, interned once (`needsDrop` asks it of every type it meets).
local var gDropName: Sym = NO_SYM;
local dropName -> Sym {
    if (gDropName == NO_SYM) { gDropName = intern("Drop"); }
    return gDropName;
}
