// Every write the parser makes to the declaration tables, as an operation that is both done here
// and logged.
//
// A package's `.klib` carries its modules' declarations as these operations rather than as the
// tables themselves (`1-cumulation/Klib.k`). Each operation carries its content (a struct's
// fields with their offsets, a trait's signatures with their parameter declarations, a template's
// parameters, fields, variants and bounds) and never an index into a table. That way a dependent
// can replay them into a registry that already holds other packages' declarations and get the
// same answers its own parse would have: `Replay.run` calls exactly the registry functions the
// parser calls through the wrappers below. Nothing in the registry is renumbered; what the tree
// points at in it (a function's bounds) is mapped by `Replay.run` as it goes.
//
// The log is one byte stream in segments, one per module, and a segment is what a dependent
// replays when it loads that module. A `macro` is parsed after the whole page, so its operations
// land in a later segment of the same module. Logging is on only while a package build parses its
// own modules (and under `--verify-regops`); the evaluator's parser (`parseExpr`) logs nothing.
#include <{ast, registry, types}>
#include <support::compiler>
#include <stdlib::{encode, map, option, string, vec}>

// ─── the records ─────────────────────────────────────────────────────────────

// A trait reference by content: what `TraitRef` points at in `traitArgs`, spelled out.
pub struct TraitUse { name: Sym, args: Vec<TypeRef> }
pub struct BoundRec { param: long, trait: TraitUse }
// One trait method's signature, with its parameters as the declarations the parser made of them.
pub struct TraitSigRec { name: Sym, returnKind: Lit, returnName: Sym, params: Vec<VarDeclNode>,
                         isStatic: bool, lentSelf: bool }

pub struct StructRec   { name: Sym, fields: Vec<FieldDef>, size: long, isEnum: bool }
pub struct BeginRec    { name: Sym, pkg: Sym }
pub struct FinishRec   { fields: Vec<FieldDef>, size: long, isEnum: bool }
pub struct EnumRec     { name: Sym, backing: Lit, variants: Vec<VariantDef>, hasPayload: bool }
pub struct TraitRec    { name: Sym, sigs: Vec<TraitSigRec>, params: Vec<TypeRef> }
pub struct DeriveRec   { trait: Sym, by: Sym, file: Sym }
pub struct ImplRec     { owner: Sym, trait: TraitUse, fns: Vec<Sym>, carried: bool }
pub struct GlobalRec   { def: GlobalDef }
pub struct AliasRec    { def: AliasDef }
pub struct DistinctRec { name: Sym, base: TypeRef }
pub struct TemplateRec { name: Sym, params: Vec<Sym>, infos: Vec<GParamInfo>, fields: Vec<GField>,
                         variants: Vec<GVariant>, bounds: Vec<BoundRec>, isEnum: bool,
                         visibility: Vis, file: Sym, pkg: Sym }
// `first` is where the producer's registry put the run: the key a function's `firstBound` is
// mapped by.
pub struct BoundsRec   { first: long, bounds: Vec<BoundRec> }
// `inBody` marks a request made while reading a non-generic body. A dependent does not check such
// a body unless it has to, so there the request is held back (`Registry.request`).
pub struct RequestRec  { base: Sym, instance: Sym, args: Vec<TypeRef>, inBody: bool }
pub struct TupleRec    { elems: Vec<TypeRef> }
pub struct FnSigRec    { params: Vec<FnParam>, ret: TypeRef }
pub struct StampRec    { base: Sym, args: Vec<TypeRef> }
pub struct MacroRec    { name: Sym }
pub struct ClosureRec  { name: Sym }
pub struct FnReturnRec { name: Sym, kind: Lit, pkg: Sym }

local OP_STRUCT: long = 1;
local OP_BEGIN: long = 2;
local OP_FINISH: long = 3;
local OP_ABANDON: long = 4;
local OP_ENUM: long = 5;
local OP_TRAIT: long = 6;
local OP_DERIVE: long = 7;
local OP_IMPL: long = 8;
local OP_GLOBAL: long = 9;
local OP_ALIAS: long = 10;
local OP_TEMPLATE: long = 11;
local OP_BOUNDS: long = 12;
local OP_REQUEST: long = 13;
local OP_TUPLE: long = 14;
local OP_FNSIG: long = 15;
local OP_STAMP: long = 16;
local OP_MACRO: long = 17;
local OP_FNRETURN: long = 18;
local OP_DISTINCT: long = 19;
local OP_CLOSURE: long = 20;

// ─── the log ─────────────────────────────────────────────────────────────────

pub var gOpLogOn: bool = false;
pub var gOpLog: Encoder;
pub var gOpCount: long = 0;
// The segments: which module each is, and where it starts and ends in `gOpLog`. The open one
// (the last) ends where the log does.
pub var gOpSegMod: Vec<long> = vec![];
pub var gOpSegStart: Vec<long> = vec![];
pub var gOpSegEnd: Vec<long> = vec![];
local var gOpCurMod: long = -1;
// Requests already logged in the open segment, so a type named a hundred times in one module is
// one record (a repeat changes nothing a replay would see).
local var gOpSeen: HashMap<str, bool> = map![];
// The package that declared each type, global and function name, so that the error for two
// packages declaring the same name can name both (two packages may each have a module `util`).
local var gDeclPkg: HashMap<str, Sym> = map![];
// The keys those two gained, in order: neither ever gains a key twice, so the keys past a mark are
// what a declaration the parser takes back added (`opsRewind`).
local var gOpSeenAdded: Vec<str> = vec![];
local var gDeclAdded: Vec<Sym> = vec![];

// Where the log stood when a declaration began, for taking it back.
pub struct OpsMark { log: long, count: long, seen: long, decl: long }

pub opsMark -> OpsMark {
    return OpsMark { log: gOpLog.len(), count: gOpCount, seen: gOpSeenAdded.len(), decl: gDeclAdded.len() };
}
// A declaration taken back: its operations off the log, and the keys it added.
pub opsRewind m:OpsMark -> void {
    gOpLog.out.truncate(m.log);
    gOpCount = m.count;
    for k in m.seen..gOpSeenAdded.len() { gOpSeen.remove(gOpSeenAdded.get(k)); }
    gOpSeenAdded.truncate(m.seen);
    for k in m.decl..gDeclAdded.len() { gDeclPkg.remove(nameOf(gDeclAdded.get(k))); }
    gDeclAdded.truncate(m.decl);
}

// The operations that follow are module `m`'s.
pub opsModule m:long -> void {
    if (!gOpLogOn || m == gOpCurMod) { return; }
    n: long = gOpSegMod.len();
    if (n > 0) { gOpSegEnd.set(n - 1, gOpLog.len()); }
    gOpOrder.push(gOpSegMod.len());
    gOpSegMod.push(m);
    gOpSegStart.push(gOpLog.len());
    gOpSegEnd.push(gOpLog.len());
    gOpCurMod = m;
    gOpSeen.clear();
    gOpSeenAdded.clear();
}
// Parsing is over: close the last segment and stop logging.
pub opsEnd -> void {
    if (!gOpLogOn) { return; }
    n: long = gOpSegMod.len();
    if (n > 0) { gOpSegEnd.set(n - 1, gOpLog.len()); }
    gOpLogOn = false;
    gOpCurMod = -1;
}
// Module `m`'s operations, every segment of them in order, appended to `out`.
pub opsOfModule m:long inout out:Encoder -> void {
    view: [u8] = "";
    unsafe { view = gOpLog.view(); }
    for k in 0..gOpSegMod.len() {
        if (gOpSegMod.get(k) == m) {
            s: long = gOpSegStart.get(k);
            out.putRaw(view[s..gOpSegEnd.get(k)]);
        }
    }
}

local logTag t:long -> void {
    gOpLog.putUvarint(t as u64);
    gOpCount = gOpCount + 1;
}

pub traitUseOf t:TraitRef -> TraitUse {
    args: Vec<TypeRef>;
    for k in 0..t.argCount { args.push(gReg.traitArgAt(t, k)); }
    return TraitUse { name: t.name, args: args };
}
local traitRefOf u:TraitUse -> TraitRef {
    return TraitRef { name: u.name, firstArg: gReg.addTraitArgs(u.args), argCount: u.args.len() };
}
local boundRecsOf bs:Vec<MethodBound> -> Vec<BoundRec> {
    out: Vec<BoundRec>;
    for k in 0..bs.len() {
        b: MethodBound = bs.get(k);
        out.push(BoundRec { param: b.param, trait: traitUseOf(b.trait) });
    }
    return out;
}
local boundsOf rs:Vec<BoundRec> -> Vec<MethodBound> {
    out: Vec<MethodBound>;
    for k in 0..rs.len() {
        out.push(MethodBound { param: rs.at(k).param, trait: traitRefOf(rs.at(k).trait) });
    }
    return out;
}

local noteDecl q:Sym pkg:Sym -> void {
    if (pkg != NO_SYM && !gDeclPkg.has(nameOf(q))) { gDeclPkg.put(nameOf(q), pkg); gDeclAdded.push(q); }
}
local declPkgOf q:Sym -> Sym {
    hit: Option<Sym> = gDeclPkg.find(nameOf(q));
    match hit { Some(p) { return p; } None { } }
    return NO_SYM;
}

// ─── the writes, as the parser makes them ────────────────────────────────────
// Each logs its record field by field, in the record's declaration order (which is what the
// derived decoder reads back), so the parser's own vectors are only lent to the log.

pub regAddStruct name:Sym fs:Vec<FieldDef> size:long isEnum:bool -> long {
    if (gOpLogOn) { logTag(OP_STRUCT); name.encode(gOpLog); fs.encode(gOpLog); size.encode(gOpLog); isEnum.encode(gOpLog); }
    return gReg.addStruct(name, fs, size, isEnum);
}
pub regBeginStruct name:Sym pkg:Sym -> long {
    noteDecl(name, pkg);
    if (gOpLogOn) { logTag(OP_BEGIN); name.encode(gOpLog); pkg.encode(gOpLog); }
    return gReg.beginStruct(name);
}
pub regFinishStruct idx:long fs:Vec<FieldDef> size:long isEnum:bool -> void {
    if (gOpLogOn) { logTag(OP_FINISH); fs.encode(gOpLog); size.encode(gOpLog); isEnum.encode(gOpLog); }
    gReg.finishStruct(idx, fs, size, isEnum);
}
pub regAbandonStruct idx:long -> void {
    if (gOpLogOn) { logTag(OP_ABANDON); }
    gReg.abandonStruct(idx);
}
pub regAddEnum name:Sym backing:Lit vs:Vec<VariantDef> hasPayload:bool -> long {
    if (gOpLogOn) { logTag(OP_ENUM); name.encode(gOpLog); backing.encode(gOpLog); vs.encode(gOpLog); hasPayload.encode(gOpLog); }
    return gReg.addEnum(name, backing, vs, hasPayload);
}

// A new trait: its signatures (each parameter run already in the tree, `a`) and its parameters.
pub regDeclareTrait name:Sym sigs:Vec<TraitMethodSig> params:Vec<TypeRef> inout a:Ast -> void {
    if (gOpLogOn) {
        logTag(OP_TRAIT);
        name.encode(gOpLog);
        gOpLog.putLen(sigs.len());
        for k in 0..sigs.len() {
            s: TraitMethodSig = sigs.get(k);
            s.name.encode(gOpLog);
            s.returnKind.encode(gOpLog);
            s.returnName.encode(gOpLog);
            gOpLog.putLen(s.paramCount);
            for j in 0..s.paramCount { d: VarDeclNode = a.decls.get(a.params.get(s.firstParam + j)); d.encode(gOpLog); }
            s.isStatic.encode(gOpLog);
            s.lentSelf.encode(gOpLog);
        }
        params.encode(gOpLog);
    }
    declareTrait(name, sigs, params);
}
local declareTrait name:Sym sigs:Vec<TraitMethodSig> params:Vec<TypeRef> -> void {
    firstMethod: long = gReg.traitMethods.len();
    gReg.traitMethods.extend(sigs);
    firstParam: long = gReg.addTraitArgs(params);
    gReg.traits.push(TraitDef { name: name, firstMethod: firstMethod, methodCount: sigs.len(),
                                firstParam: firstParam, paramCount: params.len() });
    gReg.traitAt.put(name as long, gReg.traits.len() - 1);
    if (isModuleTrait(name)) { gReg.ownedTraits.push(name); }
}

pub regNoteDerive tr:Sym by:Sym file:Sym -> void {
    if (gOpLogOn) { logTag(OP_DERIVE); tr.encode(gOpLog); by.encode(gOpLog); file.encode(gOpLog); }
    gReg.noteDerive(tr, by, file);
}
local putTraitUse t:TraitRef -> void {
    t.name.encode(gOpLog);
    gOpLog.putLen(t.argCount);
    for k in 0..t.argCount { a: TypeRef = gReg.traitArgAt(t, k); a.encode(gOpLog); }
}
local putBounds bs:Vec<MethodBound> -> void {
    gOpLog.putLen(bs.len());
    for k in 0..bs.len() { b: MethodBound = bs.get(k); b.param.encode(gOpLog); putTraitUse(b.trait); }
}
pub regAddImpl owner:Sym tr:TraitRef fns:Vec<Sym> carried:bool -> void {
    if (gOpLogOn) { logTag(OP_IMPL); owner.encode(gOpLog); putTraitUse(tr); fns.encode(gOpLog); carried.encode(gOpLog); }
    gReg.addImplAs(owner, tr, fns, carried);
}
// A global's initializer is not carried: a dependent neither checks nor runs it (the value it
// folded to is in the facts, and is what a dependent's compile-time code reads).
pub regAddGlobal g:GlobalDef -> void {
    noteDecl(g.name, g.pkg);
    if (gOpLogOn) {
        logTag(OP_GLOBAL);
        r: GlobalDef = g;
        r.init = NO_NODE;
        r.encode(gOpLog);
    }
    gReg.addGlobal(g);
}
pub regAddAlias d:AliasDef -> void {
    noteDecl(d.name, d.pkg);
    if (gOpLogOn) { logTag(OP_ALIAS); d.encode(gOpLog); }
    gReg.addAlias(d);
}
// `type X = distinct Y`: its enum is registered first (`regAddEnum`), then this says what it is.
pub regAddDistinct name:Sym base:TypeRef -> void {
    if (gOpLogOn) { logTag(OP_DISTINCT); r: DistinctRec = DistinctRec { name: name, base: base }; r.encode(gOpLog); }
    gReg.addDistinct(name, base);
}
pub regAddTemplate q:Sym params:Vec<Sym> infos:Vec<GParamInfo> fields:Vec<GField> vs:Vec<GVariant>
                   bs:Vec<MethodBound> isEnum:bool vis:Vis file:Sym pkg:Sym -> void {
    noteDecl(q, pkg);
    if (gOpLogOn) {
        logTag(OP_TEMPLATE);
        q.encode(gOpLog); params.encode(gOpLog); infos.encode(gOpLog); fields.encode(gOpLog);
        vs.encode(gOpLog); putBounds(bs); isEnum.encode(gOpLog); vis.encode(gOpLog);
        file.encode(gOpLog); pkg.encode(gOpLog);
    }
    addTemplate(q, params, infos, fields, vs, bs, isEnum, vis, file, pkg);
}
local addTemplate q:Sym params:Vec<Sym> infos:Vec<GParamInfo> fields:Vec<GField> vs:Vec<GVariant>
                  bs:Vec<MethodBound> isEnum:bool vis:Vis file:Sym pkg:Sym -> void {
    firstParam: long = gReg.addGParams(params, infos);
    firstField: long = gReg.gFields.len();
    gReg.gFields.extend(fields);
    firstVariant: long = gReg.addGVariants(vs);
    firstBound: long = gReg.addBounds(bs);
    gReg.addTemplate(GTemplate { name: q, firstParam: firstParam, paramCount: params.len(),
                                 firstField: firstField, fieldCount: fields.len(),
                                 firstVariant: firstVariant, variantCount: vs.len(),
                                 firstBound: firstBound, boundCount: bs.len(),
                                 isEnum: isEnum, visibility: vis, file: file, pkg: pkg });
}
pub regAddBounds bs:Vec<MethodBound> -> long {
    first: long = gReg.bounds.len();
    if (gOpLogOn) { logTag(OP_BOUNDS); first.encode(gOpLog); putBounds(bs); }
    return gReg.addBounds(bs);
}
pub regRequest base:Sym instance:Sym args:Vec<TypeRef> inBody:bool -> void {
    if (gOpLogOn) {
        key: String = format("{}{}", inBody as long, nameOf(instance));
        seen: str = "";
        unsafe { seen = key.view(); }
        if (!gOpSeen.has(seen)) {
            kept: str = keepString(key);
            gOpSeen.put(kept, true);
            gOpSeenAdded.push(kept);
            logTag(OP_REQUEST);
            base.encode(gOpLog); instance.encode(gOpLog); args.encode(gOpLog); inBody.encode(gOpLog);
        }
    }
    gReg.request(base, instance, args);
}
// The three that are idempotent by name: logged only when they made something.
pub regTuple elems:Vec<TypeRef> -> Sym {
    n: long = gReg.structs.len();
    out: Sym = registerTuple(elems);
    if (gOpLogOn && gReg.structs.len() != n) { logTag(OP_TUPLE); elems.encode(gOpLog); }
    return out;
}
pub regFnSig ps:Vec<FnParam> ret:TypeRef -> Sym {
    n: long = gFnSigs.sigs.len();
    out: Sym = gFnSigs.register(ps, ret);
    if (gOpLogOn && gFnSigs.sigs.len() != n) { logTag(OP_FNSIG); ps.encode(gOpLog); ret.encode(gOpLog); }
    return out;
}
pub regStampTrait base:Sym args:Vec<TypeRef> -> Sym {
    n: long = gReg.traits.len();
    out: Sym = gReg.stampTrait(base, args);
    if (gOpLogOn && gReg.traits.len() != n) { logTag(OP_STAMP); base.encode(gOpLog); args.encode(gOpLog); }
    return out;
}
pub regNoteMacro q:Sym -> void {
    if (gOpLogOn) { logTag(OP_MACRO); q.encode(gOpLog); }
    gReg.noteMacro(q);
}
// A closure's capture struct (or its template), marked before anything requests an instance.
pub regMarkClosure q:Sym -> void {
    if (gOpLogOn) { logTag(OP_CLOSURE); q.encode(gOpLog); }
    gReg.markClosure(q);
}
// What a function returns, for the type of a call to it the parser builds (`Parser.fnReturns`).
pub regFnReturn inout fr:HashMap<str, Lit> q:Sym kind:Lit pkg:Sym -> void {
    noteDecl(q, pkg);
    if (gOpLogOn) { logTag(OP_FNRETURN); q.encode(gOpLog); kind.encode(gOpLog); pkg.encode(gOpLog); }
    fr.put(nameOf(q), kind);
}


// ─── replay ──────────────────────────────────────────────────────────────────

// What a module's operations are replayed with: its file and package (when the package is a
// dependency, a request made `inBody` is held back for that file's bodies) and the structs begun
// but not yet finished. `run` is also handed the parser's table of what functions return, the
// tree a trait's parameter declarations go into, and `bounds`, which it fills with where the
// producer's registry put each run of bounds, mapped to where this one did. A function's
// `firstBound` is read through that map.
pub struct Replay { file: Sym, pkg: Sym, upstream: bool, ops: long, structAt: Vec<long> }

pub replayOf file:Sym pkg:Sym upstream:bool -> Replay {
    return Replay { file: file, pkg: pkg, upstream: upstream, ops: 0, structAt: vec![] };
}

methods Replay {

    // Two packages declaring one qualified name: the module stem is the namespace, so two
    // packages that each have a module `util` collide on everything both declare.
    clash &self q:Sym what:str -> void {
        other: Sym = declPkgOf(q);
        if (other == NO_SYM || other == self.pkg) {
            failStr(format("redefinition of `{}`\nnote: it is already declared as {}, and package `{}` declares it again", nameOf(q), what, nameOf(self.pkg)));
        }
        failStr(format("`{}` is declared by package `{}` and by package `{}`\nnote: each package has a module named `{}`, and a module's name is its namespace\nhelp: rename one of the two modules",
                       nameOf(q), nameOf(other), nameOf(self.pkg), nameOf(moduleOfName(nameOf(q)))));
    }
    typeFree &self q:Sym -> void {
        n: str = nameOf(q);
        if (gReg.findAlias(n) >= 0) { self.clash(q, "a type alias"); }
        if (gReg.hasStruct(n)) { self.clash(q, "a struct"); }
        if (gReg.findTemplate(n) >= 0) { self.clash(q, "a generic type"); }
        if (gReg.findEnum(n) >= 0) { self.clash(q, "an enum"); }
    }

    // Every operation `d` holds, applied. Fails the compile on a damaged log.
    run &self inout d:Decoder inout fr:HashMap<str, Lit> inout a:Ast inout bounds:HashMap<long, long> -> void {
        while (d.remaining() > 0 && d.ok()) {
            t: long = d.getUvarint() as long;
            self.ops = self.ops + 1;
            if (t == OP_REQUEST) {
                r: RequestRec = RequestRec.decode(d);
                was: Sym = gReg.deferIn;
                if (r.inBody && self.upstream) { gReg.deferIn = self.file; }
                gReg.request(r.base, r.instance, r.args);
                gReg.deferIn = was;
            } else if (t == OP_FNRETURN) {
                r: FnReturnRec = FnReturnRec.decode(d);
                other: Sym = declPkgOf(r.name);
                if (other != NO_SYM && other != r.pkg) { self.clash(r.name, "a function"); }
                noteDecl(r.name, r.pkg);
                fr.put(nameOf(r.name), r.kind);
            } else if (t == OP_BEGIN) {
                r: BeginRec = BeginRec.decode(d);
                self.typeFree(r.name);
                noteDecl(r.name, r.pkg);
                self.structAt.push(gReg.beginStruct(r.name));
            } else if (t == OP_FINISH) {
                r: FinishRec = FinishRec.decode(d);
                if (self.structAt.len() == 0) { d.fail("a struct finished that was never begun"); return; }
                gReg.finishStruct(self.structAt.pop(), r.fields, r.size, r.isEnum);
            } else if (t == OP_ABANDON) {
                if (self.structAt.len() == 0) { d.fail("a struct abandoned that was never begun"); return; }
                gReg.abandonStruct(self.structAt.pop());
            } else if (t == OP_STRUCT) {
                r: StructRec = StructRec.decode(d);
                if (!gReg.hasStructSym(r.name)) { gReg.addStruct(r.name, r.fields, r.size, r.isEnum); }
            } else if (t == OP_ENUM) {
                r: EnumRec = EnumRec.decode(d);
                if (gReg.findEnumSym(r.name) >= 0) { self.clash(r.name, "an enum"); }
                gReg.addEnum(r.name, r.backing, r.variants, r.hasPayload);
            } else if (t == OP_TRAIT) {
                r: TraitRec = TraitRec.decode(d);
                self.declTrait(r, a);
            } else if (t == OP_DERIVE) {
                r: DeriveRec = DeriveRec.decode(d);
                had: Sym = gReg.deriveMacroOf(r.trait);
                if (had != NO_SYM && had != r.by) {
                    failStr(format("conflicting derive macros for trait `{}`\nnote: one package derives it with `{}`, and package `{}` with `{}`",
                                   nameOf(r.trait), nameOf(had), nameOf(self.pkg), nameOf(r.by)));
                }
                if (had == NO_SYM) { gReg.noteDerive(r.trait, r.by, r.file); }
            } else if (t == OP_IMPL) {
                r: ImplRec = ImplRec.decode(d);
                gReg.addImplAs(r.owner, traitRefOf(r.trait), r.fns, r.carried);
            } else if (t == OP_GLOBAL) {
                r: GlobalRec = GlobalRec.decode(d);
                if (gReg.findGlobalSym(r.def.name) >= 0) { self.clash(r.def.name, "a global"); }
                noteDecl(r.def.name, r.def.pkg);
                gReg.addGlobal(r.def);
            } else if (t == OP_ALIAS) {
                r: AliasRec = AliasRec.decode(d);
                self.typeFree(r.def.name);
                if (r.def.visibility == Vis.Pub) {
                    other: Sym = gReg.otherPubAlias(lastComponentOf(nameOf(r.def.name)), r.def.name);
                    if (other != NO_SYM) {
                        failStr(format("type alias `{}` is published by both `{}` and `{}`\nnote: the second one comes from package `{}`",
                                       lastComponentOf(nameOf(r.def.name)), nameOf(other), nameOf(r.def.name), nameOf(self.pkg)));
                    }
                }
                noteDecl(r.def.name, r.def.pkg);
                gReg.addAlias(r.def);
            } else if (t == OP_TEMPLATE) {
                r: TemplateRec = TemplateRec.decode(d);
                // A generic function's template carries its name, which no type table holds.
                if (r.fields.len() > 0 || r.variants.len() > 0 || r.isEnum) { self.typeFree(r.name); }
                else if (gReg.findTemplateSym(r.name) >= 0) { self.clash(r.name, "a generic"); }
                noteDecl(r.name, r.pkg);
                addTemplate(r.name, r.params, r.infos, r.fields, r.variants, boundsOf(r.bounds),
                            r.isEnum, r.visibility, r.file, r.pkg);
            } else if (t == OP_BOUNDS) {
                r: BoundsRec = BoundsRec.decode(d);
                bounds.put(r.first, gReg.addBounds(boundsOf(r.bounds)));
            } else if (t == OP_TUPLE) {
                r: TupleRec = TupleRec.decode(d);
                registerTuple(r.elems);
            } else if (t == OP_FNSIG) {
                r: FnSigRec = FnSigRec.decode(d);
                gFnSigs.register(r.params, r.ret);
            } else if (t == OP_STAMP) {
                r: StampRec = StampRec.decode(d);
                gReg.stampTrait(r.base, r.args);
            } else if (t == OP_MACRO) {
                r: MacroRec = MacroRec.decode(d);
                gReg.noteMacro(r.name);
            } else if (t == OP_DISTINCT) {
                r: DistinctRec = DistinctRec.decode(d);
                gReg.addDistinct(r.name, r.base);
            } else if (t == OP_CLOSURE) {
                r: ClosureRec = ClosureRec.decode(d);
                gReg.markClosure(r.name);
            } else {
                d.fail("an operation this compiler does not know");
            }
        }
        if (self.structAt.len() > 0) { d.fail("a struct left unfinished"); }
    }

    // A trait: a repeat is fine when it says the same (a module that re-declares `Drop` rather
    // than including `core`, or `Fn2`, which any package makes when it first needs it), and a
    // conflict otherwise. A new one's parameter declarations go into the tree, where a
    // signature's parameters always are.
    declTrait &self r:TraitRec inout a:Ast -> void {
        sigs: Vec<TraitMethodSig>;
        for k in 0..r.sigs.len() {
            ps: Vec<long>;
            for j in 0..r.sigs.at(k).params.len() { a.decls.push(r.sigs.at(k).params.get(j)); ps.push(a.decls.len() - 1); }
            sigs.push(TraitMethodSig { name: r.sigs.at(k).name, returnKind: r.sigs.at(k).returnKind,
                                       returnName: r.sigs.at(k).returnName,
                                       firstParam: a.addParams(ps), paramCount: ps.len(),
                                       isStatic: r.sigs.at(k).isStatic, lentSelf: r.sigs.at(k).lentSelf });
        }
        at: long = gReg.findTraitSym(r.name);
        if (at >= 0) {
            if (!gReg.sameTrait(gReg.traitDef(at), sigs, r.params.len())) {
                failStr(format("conflicting declarations of trait `{}`\nnote: package `{}` declares it with different methods than an earlier declaration",
                               nameOf(r.name), nameOf(self.pkg)));
            }
            return;
        }
        declareTrait(r.name, sigs, r.params);
    }
}

// ─── `--verify-regops` ───────────────────────────────────────────────────────
// The whole program's log replayed into an empty registry, which must then say everything the
// parser's says: every table, entry by entry. A run of trait arguments or bounds is compared by
// what it holds rather than where it sits, since a replay builds those runs from content.

local var gVerifyBad: long = 0;
local differs what:String -> void {
    gVerifyBad = gVerifyBad + 1;
    if (gVerifyBad <= 20) { unsafe { eprintln("  regops differ: {}", what.view()); } }
}

local sameArgs ra:Registry rb:Registry a:TraitRef b:TraitRef -> bool {
    if (a.name != b.name || a.argCount != b.argCount) { return false; }
    for k in 0..a.argCount {
        if (ra.traitArgAt(a, k) != rb.traitArgAt(b, k)) { return false; }
    }
    return true;
}
local sameRun ra:Registry rb:Registry fa:long fb:long n:long -> bool {
    for k in 0..n {
        if (ra.traitArgs.get(fa + k) != rb.traitArgs.get(fb + k)) { return false; }
    }
    return true;
}
local sameBound ra:Registry rb:Registry a:MethodBound b:MethodBound -> bool {
    return a.param == b.param && sameArgs(ra, rb, a.trait, b.trait);
}

// One stretch of operations to replay: where its bytes are, the string table its names are in,
// and the module it is (`Replay`).
pub struct OpPart { at: long, len: long, symBase: long, symCount: long, file: Sym, pkg: Sym, upstream: bool }

// In a package build, the order in which operations reached the registry. Each entry is a segment
// of this compile's own log (its index), or `-1 - k` for module `k` of a loaded `.klib`, replayed
// when the scan reached it. `--klib-verify` replays them again in this order.
pub var gOpOrder: Vec<long> = vec![];
// Where this compile's own string table sits among the read ones, once it has been made readable.
pub var gOwnSymBase: long = -1;

// Makes this compile's own names readable through `Sym`'s decoder, which reading its own log
// back needs.
pub ownSymsReadable -> void {
    if (gOwnSymBase >= 0) { return; }
    gOwnSymBase = gSymIn.len();
    for s in gSymTable { gSymIn.push(s); gSymInText.push(nameOf(s)); }
}

// Segment `s` of the log, as a part.
pub logPart s:long -> OpPart {
    view: [u8] = "";
    unsafe { view = gOpLog.view(); }
    at: long = 0;
    unsafe { at = view.ptr as long; }
    return OpPart { at: at + gOpSegStart.get(s), len: gOpSegEnd.get(s) - gOpSegStart.get(s),
                    symBase: gOwnSymBase, symCount: gSymTable.len(), file: NO_SYM, pkg: NO_SYM, upstream: false };
}

// The whole log replayed and compared. Returns the number of differences (0 is a pass).
pub verifyRegops inout a:Ast fr:HashMap<str, Lit> -> long {
    opsEnd();
    ownSymsReadable();
    parts: Vec<OpPart>;
    for k in 0..gOpSegMod.len() { parts.push(logPart(k)); }
    return verifyRegopsParts(a, fr, parts);
}

// `parts` replayed, in order, into an empty registry, and compared with the one the compile has.
pub verifyRegopsParts inout a:Ast fr:HashMap<str, Lit> parts:Vec<OpPart> -> long {
    // Swapped in place (`mem::swapBytes`), so neither value is ever owned twice.
    r: Registry;
    unsafe { swapBytes(&gReg as long, &r as long, sizeof(Registry)); }
    sigs: FnSigTable;
    unsafe { swapBytes(&gFnSigs as long, &sigs as long, sizeof(FnSigTable)); }
    scratch: Ast;
    fr2: HashMap<str, Lit>;
    pi: long = 0;
    while (pi < parts.len()) {
        pt: OpPart = parts.get(pi);
        pi = pi + 1;
        gSymInBase = pt.symBase;
        gSymInCount = pt.symCount;
        view: [u8] = "";
        unsafe { view = (pt.at as *u8)[..pt.len]; }
        d: Decoder;
        unsafe { d = decoderOf(view); }
        rp: Replay = replayOf(pt.file, pt.pkg, pt.upstream);
        bmap: HashMap<long, long>;
        rp.run(&d, &fr2, &scratch, &bmap);
        if (!d.done()) {
            unsafe { swapBytes(&gReg as long, &r as long, sizeof(Registry)); }
            unsafe { swapBytes(&gFnSigs as long, &sigs as long, sizeof(FnSigTable)); }
            differs(format("part {} of the log does not decode: {} at byte {}", pi - 1, d.error(), d.pos));
            flushErr();
            return gVerifyBad;
        }
    }
    // Back again: the parser's tables in the globals, the replayed ones here.
    unsafe { swapBytes(&gReg as long, &r as long, sizeof(Registry)); }
    unsafe { swapBytes(&gFnSigs as long, &sigs as long, sizeof(FnSigTable)); }
    compareRegistries(gReg, r, a, scratch);
    if (gFnSigs.sigs.len() != sigs.sigs.len()) { differs(format("{} fn signatures, replayed {}", gFnSigs.sigs.len(), sigs.sigs.len())); }
    else {
        for i in 0..gFnSigs.sigs.len() {
            x: FnSig = gFnSigs.sigAt(i);
            y: FnSig = sigs.sigAt(i);
            same: bool = x.ret == y.ret && x.paramCount == y.paramCount;
            j: long = 0;
            while (same && j < x.paramCount) {
                p: FnParam = gFnSigs.paramAt(x, j);
                q: FnParam = sigs.paramAt(y, j);
                same = p.kind == q.kind && p.name == q.name && p.conv == q.conv;
                j = j + 1;
            }
            if (!same) { differs(format("fn signature {}", i)); }
        }
    }
    if (fr.len() != fr2.len()) { differs(format("{} function returns, replayed {}", fr.len(), fr2.len())); }
    i: long = fr.nextSlot(-1);
    while (i >= 0) {
        hit: Option<Lit> = fr2.find(fr.keyAt(i));
        match hit {
            Some(kd) { if (kd != fr.valAt(i)) { differs(format("the return of {}", fr.keyAt(i))); } }
            None { differs(format("no return replayed for {}", fr.keyAt(i))); }
        }
        i = fr.nextSlot(i);
    }
    eprintln("regops: {} operations, {} bytes, {} names; {}", gOpCount, gOpLog.len(), gSymTable.len(), plural(gVerifyBad, "difference"));
    flushErr();
    return gVerifyBad;
}

local compareRegistries x:Registry y:Registry ax:Ast ay:Ast -> void {
    if (x.structs.len() != y.structs.len()) { differs(format("{} structs, replayed {}", x.structs.len(), y.structs.len())); return; }
    for i in 0..x.structs.len() {
        s: StructDef = x.structs.get(i);
        t: StructDef = y.structs.get(i);
        same: bool = s.name == t.name && s.fieldCount == t.fieldCount && s.size == t.size && s.isEnum == t.isEnum
                     && x.findStructSym(s.name) == y.findStructSym(t.name);
        k: long = 0;
        while (same && k < s.fieldCount) { same = x.fields.get(s.firstField + k) == y.fields.get(t.firstField + k); k = k + 1; }
        if (!same) { differs(format("struct {} ({})", i, nameOf(s.name))); }
    }
    if (x.enums.len() != y.enums.len()) { differs(format("{} enums, replayed {}", x.enums.len(), y.enums.len())); return; }
    for i in 0..x.enums.len() {
        e: EnumDef = x.enums.get(i);
        f: EnumDef = y.enums.get(i);
        same: bool = e.name == f.name && e.backing == f.backing && e.hasPayload == f.hasPayload && e.variantCount == f.variantCount;
        k: long = 0;
        while (same && k < e.variantCount) { same = x.variants.get(e.firstVariant + k) == y.variants.get(f.firstVariant + k); k = k + 1; }
        same = same && x.distinctOf(e.name) == y.distinctOf(f.name);
        if (!same) { differs(format("enum {}", nameOf(e.name))); }
    }
    if (x.traits.len() != y.traits.len()) { differs(format("{} traits, replayed {}", x.traits.len(), y.traits.len())); return; }
    for i in 0..x.traits.len() {
        t: TraitDef = x.traits.get(i);
        u: TraitDef = y.traits.get(i);
        same: bool = t.name == u.name && t.methodCount == u.methodCount && t.paramCount == u.paramCount
                     && sameRun(x, y, t.firstParam, u.firstParam, t.paramCount)
                     && x.findTraitSym(t.name) == y.findTraitSym(u.name);
        k: long = 0;
        while (same && k < t.methodCount) {
            m: TraitMethodSig = x.traitMethodAt(t, k);
            n: TraitMethodSig = y.traitMethodAt(u, k);
            same = m.name == n.name && m.returnKind == n.returnKind && m.returnName == n.returnName
                   && m.paramCount == n.paramCount && m.isStatic == n.isStatic && m.lentSelf == n.lentSelf;
            j: long = 0;
            while (same && j < m.paramCount) {
                same = ax.decls.get(ax.params.get(m.firstParam + j)) == ay.decls.get(ay.params.get(n.firstParam + j));
                j = j + 1;
            }
            k = k + 1;
        }
        if (!same) { differs(format("trait {}", nameOf(t.name))); }
    }
    if (x.impls.len() != y.impls.len()) { differs(format("{} impls, replayed {}", x.impls.len(), y.impls.len())); return; }
    for i in 0..x.impls.len() {
        p: TraitImplDef = x.impls.get(i);
        q: TraitImplDef = y.impls.get(i);
        same: bool = p.structName == q.structName && p.fnCount == q.fnCount && p.carried == q.carried && sameArgs(x, y, p.trait, q.trait)
                     && x.implNext.get(i) == y.implNext.get(i);
        k: long = 0;
        while (same && k < p.fnCount) { same = x.implFns.get(p.firstFn + k) == y.implFns.get(q.firstFn + k); k = k + 1; }
        if (!same) { differs(format("impl {} of {}", nameOf(p.structName), nameOf(p.trait.name))); }
    }
    if (x.globals.len() != y.globals.len() || x.globalOrder.len() != y.globalOrder.len()) { differs(stringOf("the global count")); return; }
    for i in 0..x.globals.len() {
        g: GlobalDef = x.globals.get(i);
        h: GlobalDef = y.globals.get(i);
        if (!(g.name == h.name && g.kind == h.kind && g.structName == h.structName && g.isArray == h.isArray
              && g.count == h.count && g.visibility == h.visibility && g.file == h.file && g.pkg == h.pkg
              && g.isVar == h.isVar && x.globalOrder.get(i) == y.globalOrder.get(i))) {
            differs(format("global {}", nameOf(g.name)));
        }
    }
    if (x.aliases.len() != y.aliases.len()) { differs(stringOf("the alias count")); return; }
    for i in 0..x.aliases.len() {
        if (!(x.aliases.get(i) == y.aliases.get(i))) { differs(format("alias {}", nameOf(x.aliases.get(i).name))); }
    }
    if (x.templates.len() != y.templates.len()) { differs(stringOf("the template count")); return; }
    i: long = 0;
    while (i < x.templates.len()) {
        t: GTemplate = x.templates.get(i);
        u: GTemplate = y.templates.get(i);
        same: bool = t.name == u.name && t.paramCount == u.paramCount && t.fieldCount == u.fieldCount
                     && t.variantCount == u.variantCount && t.boundCount == u.boundCount && t.isEnum == u.isEnum
                     && t.visibility == u.visibility && t.file == u.file && t.pkg == u.pkg;
        k: long = 0;
        while (same && k < t.paramCount) {
            same = x.gParams.get(t.firstParam + k) == y.gParams.get(u.firstParam + k)
                   && x.gParamInfo.get(t.firstParam + k) == y.gParamInfo.get(u.firstParam + k);
            k = k + 1;
        }
        k = 0;
        while (same && k < t.fieldCount) { same = x.gFields.get(t.firstField + k) == y.gFields.get(u.firstField + k); k = k + 1; }
        k = 0;
        while (same && k < t.variantCount) { same = x.gVariants.get(t.firstVariant + k) == y.gVariants.get(u.firstVariant + k); k = k + 1; }
        k = 0;
        while (same && k < t.boundCount) { same = sameBound(x, y, x.bounds.get(t.firstBound + k), y.bounds.get(u.firstBound + k)); k = k + 1; }
        if (!same) { differs(format("template {}", nameOf(t.name))); }
        i = i + 1;
    }
    if (x.bounds.len() != y.bounds.len()) { differs(format("{} bounds, replayed {}", x.bounds.len(), y.bounds.len())); }
    else {
        i = 0;
        while (i < x.bounds.len()) {
            if (!sameBound(x, y, x.bounds.get(i), y.bounds.get(i))) { differs(format("bound {}", i)); }
            i = i + 1;
        }
    }
    if (x.requests.len() != y.requests.len()) { differs(format("{} requests, replayed {}", x.requests.len(), y.requests.len())); return; }
    for i in 0..x.requests.len() {
        p: GRequest = x.requests.get(i);
        q: GRequest = y.requests.get(i);
        same: bool = p.base == q.base && p.instance == q.instance && p.argCount == q.argCount
                     && x.reqDeferred.get(i) == y.reqDeferred.get(i);
        k: long = 0;
        while (same && k < p.argCount) { same = x.gArgAt(p, k) == y.gArgAt(q, k); k = k + 1; }
        if (!same) { differs(format("request {}", nameOf(p.instance))); }
    }
    if (x.closureEnvs.len() != y.closureEnvs.len()) { differs(stringOf("the closure count")); }
    i = x.closureEnvs.nextSlot(-1);
    while (i >= 0) {
        if (!y.closureEnvs.has(x.closureEnvs.keyAt(i))) { differs(format("closure {}", nameOf(x.closureEnvs.keyAt(i) as Sym))); }
        i = x.closureEnvs.nextSlot(i);
    }
    if (x.macroAt.len() != y.macroAt.len()) { differs(stringOf("the macro count")); }
    i = x.macroAt.nextSlot(-1);
    while (i >= 0) {
        if (!y.macroAt.has(x.macroAt.keyAt(i))) { differs(format("macro {}", x.macroAt.keyAt(i))); }
        i = x.macroAt.nextSlot(i);
    }
    if (x.deriveBy.len() != y.deriveBy.len()) { differs(stringOf("the derive count")); }
    i = x.deriveBy.nextSlot(-1);
    while (i >= 0) {
        key: str = x.deriveBy.keyAt(i);
        hit: Option<Sym> = y.deriveBy.find(key);
        match hit {
            Some(m) { if (m != x.deriveBy.valAt(i)) { differs(format("derive of {}", key)); } }
            None { differs(format("derive of {}", key)); }
        }
        i = x.deriveBy.nextSlot(i);
    }
}
