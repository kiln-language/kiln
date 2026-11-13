// Monomorphization: turning `Vec<T>` into `Vec_long`.
//
// A generic declaration is a pattern, not a type. The parser recorded the pattern and every use
// that asks for one; this stamps out a concrete struct per distinct argument list, so nothing
// downstream ever meets a `TypeVar`. A fixpoint, since stamping one can request another.
#include <support::compiler>
#include <parse::{ast, parser, registry, types, upstream}>
#include <facts>
#include <stdlib::{map, option, string, vec}>

// How deep an instantiation may nest before this decides the program asks for infinitely many
// types. `Vec<Vec<Vec<long>>>` written out is fine; a template that instantiates itself is not,
// and the two are indistinguishable until one of them stops.
local MAX_DEPTH: long = 64;

pub struct Mono {
    // Type parameter name -> what it stands for in the instance being stamped. One map, saved
    // and restored around a nested stamp, because laying out `Wrap<Vec<T>>` re-enters this.
    subst: HashMap<str, TypeRef>,
    // Every instance method already stamped, so a second request for the same instance -- or two
    // templates that happen to share a method name -- does not emit the function twice.
    stamped: HashMap<str, long>,
    // The template being stamped and what it is becoming, for the two things a body can name
    // that the checker cannot re-derive: `Vec { }` and `T.new()`.
    selfBase: Sym,
    selfInstance: Sym,
    // What this instance's parameters are, in order, for checking a methods block's bounds.
    selfArgs: Vec<TypeRef>,
    // The statements the clones produced, spliced into the page once the queue is drained.
    extra: Vec<long>,
    // How far into the request table stamping has got. The table is appended to as it is read.
    nextRequest: long,
    // Where each function is defined (its statement's position), by function index: a stamped
    // clone stands where its template does. Read off the page as each entry point is called.
    fnPos: Vec<long>,
    depth: long,
    // While a function is cloned in a program where two flat traits share a method name for one
    // type: each type parameter's bounds, as a run in `gHintTraits`, for `gCallHints`.
    hintVars: HashMap<str, long>,
    // The template functions by owner prefix and by name, and the implementations by type, each
    // indexed as far as its table has grown (`indexTables`, `indexImpls`).
    tmplHead: HashMap<str, long>, tmplTail: HashMap<str, long>,
    tmplFn: Vec<long>, tmplNext: Vec<long>,
    tmplByName: HashMap<str, long>,
    fnsIndexed: long,
    implHead: HashMap<long, long>, implTail: HashMap<long, long>,
    implNext: Vec<long>,
    implsIndexed: long,
    // The fingerprint of the instance being stamped (`fingerprint`), and the declared
    // implementations it is computed from, by type, as far as they have been summed.
    curFp: long,
    fpDecl: HashMap<long, long>,
    fpImplsDone: long,
    // While stamping: a clone may leave its body for later (`cloneFnAs`), and the instance is one
    // a dependency stamped already, so its methods are lazy.
    mayDefer: bool,
    lazyInstance: bool
}

// A clone whose body is stamped when something needs it (`Mono.stampBody`): the template function,
// the bindings (a run of `gLaterKeys`/`gLaterVals`), the instance whose method it is, and whose
// code it is and where, for errors. Per function index, through `gLaterAt`.
pub struct LaterBody { tmpl: long, firstSubst: long, substCount: long, selfBase: Sym, selfInstance: Sym,
                       owner: Sym, pos: long }
pub var gLater: Vec<LaterBody> = vec![];
pub var gLaterAt: HashMap<long, long> = map![];
pub var gLaterKeys: Vec<str> = vec![];
pub var gLaterVals: Vec<TypeRef> = vec![];
// How many bodies were stamped late, for `--time-phases`.
pub var gLaterStamped: long = 0;
// The struct literals a template's method wrote with the bare template name (`Pair { .. }` inside
// `methods Pair<A, B>`), by literal index. A clone types each as its own instance (`Pair<long,
// int>`), which is what it means where nothing else says; where it is stored into a different
// instance of the same template (`-> Pair<B, A>`), the checker aims it there instead
// (`Checker.aimSelfLit`), as it aims a template literal written outside the template.
pub var gSelfLits: HashMap<long, bool> = map![];

// One step of a 64-bit mix (splitmix's finalizer), so a sum of fingerprints does not cancel.
local FP_M1: long = -4658895280553007687;     // 0xBF58476D1CE4E5B9
local FP_M2: long = -7723592293110705685;     // 0x94D049BB133111EB
local fpMix x0:long -> long {
    x: u64 = x0 as u64;
    x = (x ^ (x >> 30)) * (FP_M1 as u64);
    x = (x ^ (x >> 27)) * (FP_M2 as u64);
    return (x ^ (x >> 31)) as long;
}

methods Mono for Default {
    new -> Mono {
        return Mono { subst: map![], stamped: map![], selfBase: NO_SYM, selfInstance: NO_SYM,
                      selfArgs: vec![], extra: vec![], nextRequest: 0, fnPos: vec![], depth: 0,
                      hintVars: map![],
                      tmplHead: map![], tmplTail: map![], tmplFn: vec![], tmplNext: vec![],
                      tmplByName: map![], fnsIndexed: 0,
                      implHead: map![], implTail: map![], implNext: vec![], implsIndexed: 0,
                      curFp: 0, fpDecl: map![], fpImplsDone: 0, mayDefer: false, lazyInstance: false };
    }
}

methods Mono {
    // Drain the request queue, stamping each instance. Stamping appends more requests, so this
    // re-reads the length every time rather than taking it once.
    run &self inout a:Ast page:long -> long {
        self.indexFnPos(a, page);
        self.drainRequests(a);
        self.relayout();
        // The page gains the stamped methods. A block is a contiguous run, so the page is rebuilt
        // rather than appended to.
        if (self.extra.len() == 0) { return page; }
        b: Block = a.blocks.get(page);
        ids: Vec<long>;
        for k in 0..b.stmtCount { ids.push(a.stmtRuns.get(b.firstStmt + k)); }
        ids.extend(self.extra);
        return a.addBlock(ids);
    }

    // Every struct, laid out again now that the instances its fields name exist. A struct is
    // laid out when it is parsed, and a field whose type is a generic instance had no size then:
    // `SpinLock` holds an `AtomicInt`, which is `Atomic<int>`, which nothing had stamped yet, so
    // it took zero bytes and every field after it landed on top of it. That is how a mutex's
    // guarded value came to share an address with the lock flag protecting it.
    //
    // Repeated to a fixpoint: a struct that gains a size gives every struct holding it a
    // different answer too.
    relayout &self -> void {
        changed: bool = true;
        rounds: long = 0;
        while (changed && rounds < MAX_DEPTH) {
            changed = false;
            for i in 0..gReg.structCount() {
                if (gReg.relayoutStruct(i)) { changed = true; }
            }
            rounds = rounds + 1;
        }
    }

    // Every type instance asked for that has not been stamped. The table grows as it is walked (
    // laying out `Vec<Option<T>>` asks for `Option<T>`) so the index, not a snapshot length, is
    // what says when it is drained. Resumable: a generic function's body can ask for more.
    drainRequests &self inout a:Ast -> void {
        loop {
            while (self.nextRequest < gReg.requestCount()) {
                at: long = self.nextRequest;
                self.nextRequest = self.nextRequest + 1;
                // Asked for only by a dependency's body this compile does not check: held until
                // something that is checked asks too (see `Registry.request`).
                if (gReg.isDeferred(at)) { continue; }
                self.stampRequest(a, at);
            }
            // Held ones let go since: already passed over by the index, so stamped from here.
            if (!gReg.hasReleased()) { break; }
            released: Vec<long> = gReg.takeReleased();
            for k in 0..released.len() {
                if (released.get(k) < self.nextRequest) { self.stampRequest(a, released.get(k)); }
            }
        }
    }

    // Requests made since the last drain: a body stamped late (`stampBody`) can name an instance
    // nothing had asked for, and the driver's rounds go on until it is stamped.
    pendingRequests &self -> bool { return gReg.requestCount() > self.nextRequest || gReg.hasReleased(); }

    stampRequest &self inout a:Ast at:long -> void {
        r: GRequest = gReg.requestAt(at);
        if (gReg.isPatternRequest(r)) { return; }
        args: Vec<TypeRef>;
        for k in 0..r.argCount { args.push(gReg.gArgAt(r, k)); }
        // What is wrong with an instance is reported where it was asked for.
        was: long = gPos;
        if (gReg.requestPos(at) != 0) { gPos = gReg.requestPos(at); }
        self.stamp(a, r.base, r.instance, args);
        gPos = was;
    }

    // Where each function on the page is defined, by its index. One pass over the page.
    indexFnPos &self inout a:Ast page:long -> void {
        n: long = a.blockLen(page);
        for k in 0..n {
            st: Stmt = a.stmtAt(page, k);
            if (st.kind == StmtKind.FunctionDef) {
                while (self.fnPos.len() <= st.at) { self.fnPos.push(0); }
                self.fnPos.set(st.at, a.stmtPos.get(a.stmtIdAt(page, k)));
            }
        }
    }

    // `Clone` for a struct that never wrote one. Field by field: a field that owns something
    // clones, everything else copies, which is exactly what makes the derived clone deep where
    // it has to be and free where it does not. Synthesized on demand, because a struct nobody
    // clones needs no clone: the checker names the ones a call actually asked for.
    deriveClones &self inout a:Ast page:long want:Vec<Sym> -> long {
        self.indexFnPos(a, page);
        self.extra.clear();
        for i in 0..want.len() {
            self.deriveClone(a, want.get(i));
        }
        if (self.extra.len() == 0) { return page; }
        b: Block = a.blocks.get(page);
        ids: Vec<long>;
        for k in 0..b.stmtCount { ids.push(a.stmtRuns.get(b.firstStmt + k)); }
        ids.extend(self.extra);
        return a.addBlock(ids);
    }

    deriveClone &self inout a:Ast owner:Sym -> void {
        name: Sym = methodName(owner, intern("clone"));
        if (self.stamped.find(nameOf(name)).isSome()) { return; }
        at: long = gReg.findStruct(nameOf(owner));
        if (at < 0) { return; }
        self.stamped.put(nameOf(name), 1);
        d: StructDef = gReg.structDef(at);

        // `self`, lent: the clone reads the original and does not consume it.
        selfName: Sym = intern("self");
        a.decls.push(VarDeclNode { name: selfName, kind: Lit.Ref, structName: owner,
                                   isArray: false, count: 0, conv: Conv.None, isVariadic: false,
                                   elemKind: Lit.Void, elemStruct: NO_SYM, init: NO_NODE });
        params: Vec<long>;
        params.push(a.decls.len() - 1);

        body: Vec<long>;
        ei: long = NOT_FOUND;
        if (d.isEnum && gReg.needsDrop(owner)) { ei = gReg.findEnum(nameOf(owner)); }
        if (ei >= 0) {
            // A sum type's payloads overlap, so field by field would clone every variant's
            // payload out of whichever one is live. One arm per variant instead, each building
            // that variant from its own payload: `if (self.$tag == A) { return K.A(self.$A$0.clone()); }`.
            ed: EnumDef = gReg.enumDef(ei);
            for v in 0..ed.variantCount {
                vd: VariantDef = gReg.variantAt(ed, v);
                inits: Vec<InitNode>;
                inits.push(InitNode { name: intern(enumTagField()),
                                      value: a.leaf(Op.Literal, Payload.Num(vd.value), ed.backing) });
                for j in 0..vd.payloadCount {
                    pf: Sym = enumPayloadField(nameOf(vd.name), j);
                    fi: long = gReg.findFieldSym(d, pf);
                    if (fi >= 0) {
                        inits.push(InitNode { name: pf, value: self.cloneOfField(a, selfName, owner, gReg.fieldAt(d, fi)) });
                    }
                }
                a.returns.push(ReturnNode { value: self.cloneLit(a, owner, inits) });
                ret: long = a.addStmt(StmtKind.Return, a.returns.len() - 1);
                if (v == ed.variantCount - 1) { body.push(ret); }
                else {
                    recv: NodeId = a.leafOf(Op.Lvalue, Payload.Name(selfName), Lit.Ref, owner);
                    a.fields.push(FieldNode { base: recv, name: intern(enumTagField()) });
                    tag: NodeId = a.leafOf(Op.FieldAccess, Payload.Field(a.fields.len() - 1),
                                           ed.backing, NO_SYM);
                    test: NodeId = a.binary(Op.IsEqual, tag,
                                            a.leaf(Op.Literal, Payload.Num(vd.value), ed.backing), Lit.Int);
                    arm: Vec<long>;
                    arm.push(ret);
                    a.ifs.push(IfNode { cond: test, body: a.addBlock(arm), elseIf: -1 });
                    body.push(a.addStmt(StmtKind.If, a.ifs.len() - 1));
                }
            }
        } else {
            inits: Vec<InitNode>;
            for k in 0..d.fieldCount {
                f: FieldDef = gReg.fieldAt(d, k);
                inits.push(InitNode { name: f.name, value: self.cloneOfField(a, selfName, owner, f) });
            }
            a.returns.push(ReturnNode { value: self.cloneLit(a, owner, inits) });
            body.push(a.addStmt(StmtKind.Return, a.returns.len() - 1));
        }
        firstArg: long = a.params.len();
        a.params.extend(params);
        a.fns.push(FnNode { name: name, returnKind: Lit.Struct, returnStruct: owner,
                            visibility: Vis.Pub, file: NO_SYM, pkg: NO_SYM,
                            isUnsafe: false, isTemplate: false, inferReturn: false,
                            firstBound: 0, boundCount: 0, firstArg: firstArg, argCount: params.len(),
                            body: a.addBlock(body) });
        self.extra.push(a.addStmt(StmtKind.FunctionDef, a.fns.len() - 1));

        fns: Vec<Sym>;
        fns.push(name);
        gReg.addImpl(owner, TraitRef { name: intern("Clone"), firstArg: 0, argCount: 0 }, fns);
    }

    // `self.f` for a derived clone: cloned when the field owns something (the checker allowed the
    // derive only when it has a clone of its own), copied otherwise, which is what `Copy` means.
    cloneOfField &self inout a:Ast selfName:Sym owner:Sym f:FieldDef -> NodeId {
        recv: NodeId = a.leafOf(Op.Lvalue, Payload.Name(selfName), Lit.Ref, owner);
        a.fields.push(FieldNode { base: recv, name: f.name });
        v: NodeId = a.leafOf(Op.FieldAccess, Payload.Field(a.fields.len() - 1), f.kind, f.structName);
        if (f.kind == Lit.Struct && !f.isArray
            && (gReg.needsDrop(f.structName) || gReg.structImplements(nameOf(f.structName), intern("Clone")))) {
            a.calls.push(CallNode { name: intern("clone"), receiver: v,
                                    firstArg: 0, argCount: 0, slot: NO_SLOT,
                                    callee: NO_NODE, sigKey: NO_SYM });
            v = a.leafOf(Op.MethodCall, Payload.Call(a.calls.len() - 1), Lit.Struct, f.structName);
        }
        return v;
    }
    cloneLit &self inout a:Ast owner:Sym inits:Vec<InitNode> -> NodeId {
        first: long = a.inits.len();
        a.inits.extend(inits);
        a.lits.push(LitNode { typeName: owner, firstInit: first, initCount: inits.len(), rest: NO_NODE });
        return a.leafOf(Op.StructLit, Payload.Lit(a.lits.len() - 1), Lit.Struct, owner);
    }

    // The generic functions a check pass asked for. Unlike a type, a function is instantiated by
    // a call (its arguments are what say what its parameters are) so the requests arrive from
    // the checker rather than from the parser, and the page grows by one definition each.
    stampFunctions &self inout a:Ast page:long reqs:Vec<FnRequest> -> long {
        self.indexFnPos(a, page);
        self.extra.clear();
        i: long = 0;
        while (i < reqs.len()) {
            r: FnRequest = reqs.get(i);
            if (self.stamped.find(nameOf(r.instance)).isSome()) { i = i + 1; continue; }
            at: long = self.fnDefOf(a, r.base);
            if (at < 0) { i = i + 1; continue; }
            tat: long = gReg.findTemplate(nameOf(r.base));
            if (tat < 0) { i = i + 1; continue; }
            t: GTemplate = gReg.templateDef(tat);

            self.subst.clear();
            fargs: Vec<TypeRef>;
            k: long = 0;
            while (k < t.paramCount && k < r.argCount) {
                self.subst.put(nameOf(gReg.gParamAt(t, k)), gReg.genericArgAt(r.firstArg, k));
                fargs.push(gReg.genericArgAt(r.firstArg, k));
                k = k + 1;
            }
            self.selfBase = NO_SYM;
            self.selfInstance = NO_SYM;
            self.curFp = self.fingerprint(r.base, fargs);
            self.mayDefer = true;
            self.cloneFnAs(a, at, r.instance);
            self.mayDefer = false;
            i = i + 1;
        }
        // A stamped body names types the program had not asked for until now (`sort<long>`'s
        // `Vec<long>`) and those instances have to exist before it is checked. And be laid out:
        // an instance stamped here has fields whose own instances were stamped after it, at
        // zero bytes -- `Vec<long>` first, the `RawVec<long>` in its `buf` next -- exactly as
        // at the first pass, which is why that one relays out to a fixpoint. Without this a
        // `Vec<long>` reached only through inference -- `vecOf(1 as long)`, no `Vec<long>`
        // written anywhere -- was eight bytes wide, and a temporary holding one copied a third
        // of it.
        self.selfBase = NO_SYM;
        self.selfInstance = NO_SYM;
        self.subst.clear();
        self.drainRequests(a);
        self.relayout();
        if (self.extra.len() == 0) { return page; }
        b: Block = a.blocks.get(page);
        ids: Vec<long>;
        for k in 0..b.stmtCount { ids.push(a.stmtRuns.get(b.firstStmt + k)); }
        ids.extend(self.extra);
        return a.addBlock(ids);
    }

    // Where a function template's definition sits. The pattern is left in the tree precisely so
    // its clones can be made from it.
    fnDefOf &self inout a:Ast name:Sym -> long {
        self.indexTables(a);
        return self.tmplByName.getOr(nameOf(name), NOT_FOUND);
    }

    // ─── substitution ────────────────────────────────────────────────────────

    // A type as written in a template, under the current bindings. A bare `T` becomes what T is
    // bound to; `*T` and `[T]` rebuild their companion around the substituted element, since both
    // carry it as a mangled name rather than as a nested type.
    concrete &self t:TypeRef -> TypeRef {
        if (t.base == Lit.TypeVar) {
            hit: Option<TypeRef> = self.subst.find(nameOf(t.name));
            match hit { Some(bound) { return bound; } None { } }
            return t;                            // still symbolic: an enclosing stamp will bind it
        }
        if (t.base == Lit.Ptr) {
            inner: TypeRef = self.concreteNamed(t.name);
            return TypeRef { base: Lit.Ptr, name: intern(typeMangleName(inner.base, inner.name)) };
        }
        if (t.base == Lit.Slice) {
            inner: TypeRef = self.concreteNamed(t.name);
            return TypeRef { base: Lit.Slice, name: intern(sliceElemName(inner.base, inner.name)) };
        }
        if (t.base == Lit.Struct) { return TypeRef { base: Lit.Struct, name: self.substTypeName(t.name) }; }
        // `fn(A) -> R` carries a key into the signature table, so substituting one is not a
        // lookup of a name: the whole signature is rebuilt under the bindings and registered
        // again, and the concrete key is what the clone carries. Every part travels: a
        // parameter's type, the result, and the convention, which is the half of a fn type that
        // decides who releases the argument and so cannot be dropped in the rebuild.
        //
        // Left unsubstituted, `mapOption<long, long>`'s `f: fn(T)->U` kept the pattern's key, so
        // `g(v)` was typed as a struct called `U`, a call given a hidden destination pointer
        // whose address was then stored as the payload.
        if (t.base == Lit.Fn) {
            at: long = gFnSigs.find(t.name);
            if (at < 0) { return t; }
            sig: FnSig = gFnSigs.sigAt(at);
            ps: Vec<FnParam>;
            for k in 0..sig.paramCount {
                p: FnParam = gFnSigs.paramAt(sig, k);
                q: TypeRef = self.concrete(fnParamType(p));
                ps.push(fnParamOf(q, p.conv));
            }
            ret: TypeRef = self.concrete(sig.ret);
            return TypeRef { base: Lit.Fn, name: gFnSigs.register(ps, ret) };
        }
        if (t.base == Lit.Ref) {
            inner: TypeRef = self.concreteNamed(t.name);
            // A backed enum spells like a struct but is its integer, and a borrow of a scalar is
            // the scalar: `&T` at T = a backed enum made a ref of it, so `Vec<Sym>.at(i)` handed
            // back the element's address where the element was asked for.
            if (inner.base == Lit.Struct && !namedScalar(inner.base, inner.name)) { return TypeRef { base: Lit.Ref, name: inner.name }; }
            return inner;                        // a borrow of a scalar is the scalar
        }
        return t;
    }

    // A companion name under the current bindings. `*T` and `[T]` record their element as the
    // spelling `typeMangleName` produced, so substituting one is a lookup by that spelling.
    concreteNamed &self n:Sym -> TypeRef {
        if (n == NO_SYM) { return TypeRef { base: Lit.Void, name: NO_SYM }; }
        // The template's own name inside its own methods: `self` is declared as `Atomic`, and in
        // this clone that means `Atomic_int`.
        if (n == self.selfBase) { return TypeRef { base: Lit.Struct, name: self.selfInstance }; }
        hit: Option<TypeRef> = self.subst.find(nameOf(n));
        match hit { Some(bound) { return bound; } None { } }
        if (namesScalar(nameOf(n))) { return TypeRef { base: scalarNamed(nameOf(n)), name: NO_SYM }; }
        if (isTupleName(n)) { return TypeRef { base: Lit.Struct, name: self.substTuple(n) }; }
        // Not a parameter itself, but possibly an instance of one: `Vec_T` under T = long is
        // `Vec_long`. Every path that resolves a companion name comes through here, so this is
        // where that has to happen: a borrow of a `Vec<T>` needs it as much as a value does.
        return TypeRef { base: Lit.Struct, name: self.substInstance(n) };
    }

    // An array length as written in a template under the current bindings: `[u8; N]` recorded
    // the parameter (`countOfParam`), and this instance's N is its value.
    concreteCount &self c:long -> long {
        if (!isParamCount(c)) { return c; }
        p: Sym = paramOfCount(c);
        hit: Option<TypeRef> = self.subst.find(nameOf(p));
        match hit {
            Some(b) {
                if (b.base == Lit.Len) { return lengthValue(b); }
                failStr(format("'{}' is an array's length here, and it was given the type {}",
                               nameOf(p), self.spellArg(b)));
            }
            None { }
        }
        return c;                                // still symbolic: an enclosing stamp will bind it
    }

    // Each argument is the kind of thing its parameter is: a length for `N: long`, a type for
    // the rest. The parser holds every use it can see to this; an argument a template's own body
    // passed along (`Buf<T, N>` inside another template) is only known now.
    requireKinds &self base:Sym t:GTemplate args:Vec<TypeRef> -> void {
        k: long = 0;
        while (k < t.paramCount && k < args.len()) {
            isLen: bool = args.get(k).base == Lit.Len;
            if (gReg.gParamIsLen(t, k) && !isLen) {
                failStr(format("'{}' is a length parameter of {}, and it was given the type {}",
                               nameOf(gReg.gParamAt(t, k)), nameOf(base), self.spellArg(args.get(k))));
            }
            if (!gReg.gParamIsLen(t, k) && isLen) {
                failStr(format("'{}' is a type parameter of {}, and it was given the length {}",
                               nameOf(gReg.gParamAt(t, k)), nameOf(base), nameOf(args.get(k).name)));
            }
            k = k + 1;
        }
    }

    // ─── stamping ────────────────────────────────────────────────────────────

    stamp &self inout a:Ast base:Sym instance:Sym args:Vec<TypeRef> -> void {
        if (gReg.hasStruct(nameOf(instance))) { return; }        // already stamped
        at: long = gReg.findTemplate(nameOf(base));
        if (at < 0) { return; }                                  // not generic: already itself
        t: GTemplate = gReg.templateDef(at);
        // An error about this instance (its bounds, its arguments) stands at the request; its
        // notes follow the chain from whoever's code asked.
        outer: Sym = gCtxInst;
        gCtxInst = originOf(instance).parent;
        if (args.len() != t.paramCount) {
            failStr(format("{} takes {} type argument(s) but was given {}",
                           nameOf(base), t.paramCount, args.len()));
        }
        self.depth = self.depth + 1;
        if (self.depth > MAX_DEPTH) {
            failStr(format("{} instantiates itself without end — a generic type may hold a POINTER to itself, never a value of itself",
                           nameOf(base)));
        }

        // Bind this instance's parameters. Nothing to save and restore yet: a field whose type is
        // itself generic was already recorded as its own request by the parser, so a stamp does
        // not re-enter another one.
        self.subst.clear();
        for k in 0..t.paramCount {
            self.subst.put(nameOf(gReg.gParamAt(t, k)), args.get(k));
        }
        self.requireKinds(base, t, args);

        // A bound the type declared holds for every instance of it, unlike a methods block's,
        // which is conditional. `struct Wrap<W: Default>` stamped with a W that is not `Default`
        // has fields it cannot initialize, and used to be stamped anyway.
        for b in 0..t.boundCount {
            mb: MethodBound = gReg.boundAt(t.firstBound + b);
            if (mb.param >= args.len()) { continue; }
            if (self.satisfies(args.get(mb.param), mb.trait.name)) { continue; }
            failStr(format("{} does not implement '{}', required by {}<{}>",
                           self.spellArg(args.get(mb.param)), lastComponentOf(nameOf(mb.trait.name)),
                           nameOf(base), nameOf(gReg.gParamAt(t, mb.param))));
        }

        gCtxInst = instance;          // what its fields ask for, it asks for
        if (t.isEnum) { self.stampEnum(t, instance); } else { self.stampStruct(t, instance); }
        gCtxInst = outer;
        self.selfBase = base;
        self.selfInstance = instance;
        self.curFp = self.fingerprint(base, args);
        self.selfArgs = args;
        firstClone: long = a.fns.len();
        self.lazyInstance = gKnownInstances.has(nameOf(instance));
        self.mayDefer = true;
        self.cloneMethods(a, base, instance);
        self.mayDefer = false;
        self.lazyInstance = false;
        // A dependency stamped this instance, and checked every method of it then: here they
        // are compiled only if something reaches them.
        if (gKnownInstances.has(nameOf(instance))) { markLazy(firstClone, a.fns.len()); }
        self.depth = self.depth - 1;
    }

    stampStruct &self t:GTemplate instance:Sym -> void {
        fields: Vec<FieldDef>;
        cursor: long = 0;
        for k in 0..t.fieldCount {
            f: GField = gReg.gFieldAt(t, k);
            ft: TypeRef = self.concrete(f.kind);
            want: FieldDef = FieldDef { name: f.name, kind: ft.base, structName: ft.name,
                                        offset: 0, isArray: f.isArray, count: self.concreteCount(f.count) };
            p: Placed = placeField(cursor, want);
            fields.push(p.field);
            cursor = p.next;
        }
        gReg.addStruct(instance, fields, alignUp(cursor, 8), false);
    }

    // A generic sum type, laid out exactly as a written-out one: the tag, then every variant's
    // payload from one shared offset, so the variants overlap. Registered both as an enum (which
    // is what `match` reads to know the variants and their tags) and as a struct (which is what
    // a field access and the layout read).
    stampEnum &self t:GTemplate instance:Sym -> void {
        payloads: Vec<FieldDef>;
        variants: Vec<VariantDef>;
        hasPayload: bool = false;
        for k in 0..t.variantCount {
            gv: GVariant = gReg.gVariantAt(t, k);
            first: long = payloads.len();
            for j in 0..gv.payloadCount {
                f: GField = gReg.gFieldAt(t, first + j);
                ft: TypeRef = self.concrete(f.kind);
                payloads.push(FieldDef { name: f.name, kind: ft.base, structName: ft.name,
                                         offset: 0, isArray: false, count: 0 });
            }
            if (gv.payloadCount > 0) { hasPayload = true; }
            variants.push(VariantDef { name: gv.name, value: gv.value,
                                       firstPayload: first, payloadCount: gv.payloadCount });
        }
        size: long = layoutEnum(instance, Lit.Int, &variants, &payloads);
        // The tag is field zero; the payloads keep the offsets the layout gave them.
        fields: Vec<FieldDef>;
        fields.push(FieldDef { name: intern(enumTagField()), kind: Lit.Int, structName: NO_SYM,
                               offset: 0, isArray: false, count: 0 });
        fields.extend(payloads);
        gReg.addStruct(instance, fields, size, true);
        gReg.addEnum(instance, Lit.Int, variants, hasPayload);
    }

    // ─── cloning a template's methods ────────────────────────────────────────
    //
    // Every function named `<base>_something` is copied to `<instance>_something` with the type
    // parameters substituted. The AST is an index arena, so a clone is a copy of every node the
    // body reaches, appended, with each index remapped to where its copy landed.
    //
    // Call names inside the body are deliberately not rewritten: `self.push(x)` is still an
    // unresolved method call at this point, and the checker resolves it from the receiver's
    // type, which is now the instance. Only what the checker cannot re-derive is substituted:
    // declared types, and a struct literal that names the template.

    // The template's methods are named `Base_m`, so the prefix finds them, but this appends to
    // the same list, and a clone's name carries the prefix too: `Atomic_int_cas` would match while
    // stamping `Atomic<long>` and be cloned again as `Atomic_long_int_cas`. Only a template is a
    // pattern; a clone is already a definition.
    cloneMethods &self inout a:Ast base:Sym instance:Sym -> void {
        baseLen: long = nameOf(base).len;
        // Every template named `<base>_...`, in the order they were made: the ones that exist
        // now. What this stamp adds (a method's own generic copy) is not walked again here.
        self.indexTables(a);
        f: long = self.tmplHead.getOr(nameOf(base), -1);
        while (f >= 0) {
            at: long = self.tmplFn.get(f);
            f = self.tmplNext.get(f);
            fn: FnNode = a.fns.get(at);
            // An instance's own copy of a generic method is a template too, but of a function,
            // not of this type's methods.
            if (!fn.isTemplate || self.stamped.has(nameOf(fn.name))) { continue; }
            // A method that implements a trait is named by `cloneImpls`, from the trait at this
            // instance's arguments. Naming it here as well would name it twice, and the textual
            // name would be the wrong one: see the note there.
            if (!self.isImplMethod(base, fn.name) && self.meetsBounds(fn)) {
                self.cloneFn(a, at, instance, baseLen);
            }
        }
        self.cloneImpls(a, base, instance);
    }

    // Is this template method the implementation of some trait, rather than an inherent one?
    isImplMethod &self base:Sym name:Sym -> bool {
        self.indexImpls();
        i: long = self.implHead.getOr(base as long, -1);
        while (i >= 0) {
            im: TraitImplDef = gReg.implAt(i);
            for k in 0..im.fnCount {
                if (gReg.implFnAt(im, k) == name) { return true; }
            }
            i = self.implNext.get(i);
        }
        return false;
    }

    // ─── the indexes a stamp reads ───────────────────────────────────────────
    //
    // A stamp needs its template's methods, its implementations, and a template function by
    // name. Walking every function and every implementation of the program for each of those
    // was a third of a small package's compile once its dependencies' templates were all in the
    // tree. Both tables only ever grow at the end, so each is indexed up to where it has got.

    // Template functions: under every prefix of its name that ends where an `_` begins (so
    // `vec::Vec_long_map` is under `vec::Vec` and `vec::Vec_long`: exactly the bases whose
    // `<base>_` it starts with), and by its own name, first one wins.
    indexTables &self inout a:Ast -> void {
        while (self.fnsIndexed < a.fns.len()) {
            at: long = self.fnsIndexed;
            self.fnsIndexed = at + 1;
            fn: FnNode = a.fns.get(at);
            if (!fn.isTemplate) { continue; }
            name: str = nameOf(fn.name);
            if (!self.tmplByName.has(name)) { self.tmplByName.put(name, at); }
            for i in 0..name.len {
                if (charAt(name, i) != '_') { continue; }
                key: str = strSlice(name, 0, i);
                node: long = self.tmplFn.len();
                self.tmplFn.push(at);
                self.tmplNext.push(-1);
                tail: long = self.tmplTail.getOr(key, -1);
                if (tail < 0) { self.tmplHead.put(key, node); } else { self.tmplNext.set(tail, node); }
                self.tmplTail.put(key, node);
            }
        }
    }

    // ─── an instance another package compiled ────────────────────────────────
    //
    // A package's instance functions are exported (`asm`'s alias), each with what it was
    // compiled against. One made here that a dependency compiled against exactly what this
    // compile sees is that dependency's: linked, never compiled again (PORT.md, packages part 3).

    // Clone `at`, just made: linked to a dependency's copy if there is a fitting one.
    reuseOf &self inout a:Ast at:long e:long -> void {
        f: FnNode = a.fns.get(at);
        x: InstExport = gInstExports.get(e);
        markExtern(at);
        noteFnFact(at, x.fact);
        gLinkAlias.put(nameOf(f.name), nameOf(x.alias));
        // A closure's return its owner's compile settled, as a dependency's own function's is.
        if (f.inferReturn) {
            fact: FnFact = gFacts.fns.get(x.fact);
            f.returnKind = fact.retKind;
            f.returnStruct = fact.retStruct;
            f.inferReturn = false;
            a.fns.set(at, f);
        }
    }

    // Clone `at` (about to be pushed) of template function `tmpl` left without its body: what
    // stamping it later needs, under the bindings in force now.
    noteLater &self at:long tmpl:long owner:Sym -> void {
        first: long = gLaterKeys.len();
        keys: Vec<str> = self.subst.keys();
        for k in 0..keys.len() {
            gLaterKeys.push(keys.get(k));
            gLaterVals.push(self.subst.get(keys.get(k)));
        }
        gLaterAt.put(at, gLater.len());
        gLater.push(LaterBody { tmpl: tmpl, firstSubst: first, substCount: keys.len(),
                                selfBase: self.selfBase, selfInstance: self.selfInstance,
                                owner: owner, pos: gPos });
    }

    // The body of clone `at`, stamped now that something needs it: under the bindings it was
    // made with, exactly as `cloneFnAs` would have. Answers whether that asked for an instance
    // the program had not asked for, which has to be stamped before the body is checked.
    stampBody &self inout a:Ast at:long -> bool {
        r: long = gLaterAt.getOr(at, -1);
        if (r < 0) { failStr(format("internal: '{}' has no body to stamp", nameOf(a.fns.get(at).name))); }
        lb: LaterBody = gLater.get(r);
        self.subst.clear();
        for k in 0..lb.substCount { self.subst.put(gLaterKeys.get(lb.firstSubst + k), gLaterVals.get(lb.firstSubst + k)); }
        self.selfBase = lb.selfBase;
        self.selfInstance = lb.selfInstance;
        was: long = gPos;
        wasInst: Sym = gCtxInst;
        gPos = lb.pos;
        gCtxInst = lb.owner;
        tmpl: FnNode = a.fns.get(lb.tmpl);
        self.hintVars.clear();
        if (!gReg.carriedOwners.isEmpty()) { self.noteHintVars(tmpl); }
        asked: long = gReg.requestCount();
        body: long = self.cloneBlock(a, tmpl.body);
        f: FnNode = a.fns.get(at);
        f.body = body;
        a.fns.set(at, f);
        self.hintVars.clear();
        gPos = was;
        gCtxInst = wasInst;
        gLaterStamped = gLaterStamped + 1;
        return gReg.requestCount() > asked;
    }

    // What the instance `base<args>` is compiled against: every type it is made of -- the
    // template, the arguments, and through them an instance's own template and arguments and a
    // struct's fields -- each with the traits the source declares for it. A sum, so the order the
    // types are met in does not matter: the owner and a dependent meet them differently. Two
    // compiles that agree on this compile the instance's functions to the same code (Kiln has no
    // coherence rule: any package may implement `Drop` for a type it did not write, and the
    // fingerprint is how a dependent notices one its dependency could not see).
    fingerprint &self base:Sym args:Vec<TypeRef> -> long {
        if (!gKlibMode) { return 0; }
        seen: HashMap<long, bool>;
        acc: long = self.fpVisit(base, &seen);
        for k in 0..args.len() { acc = acc + self.fpType(args.get(k), &seen); }
        return acc;
    }
    fpType &self t:TypeRef inout seen:HashMap<long, bool> -> long {
        if (t.base == Lit.Len) { return 0; }                 // in the instance's name already
        if (t.name != NO_SYM) { return self.fpVisit(t.name, seen); }
        return self.fpVisit(intern(typeName(t.base)), seen);
    }
    // `n`'s share, and that of everything it is made of not met yet.
    fpVisit &self n:Sym inout seen:HashMap<long, bool> -> long {
        if (n == NO_SYM || seen.has(n as long)) { return 0; }
        seen.put(n as long, true);
        acc: long = fpMix(strHash(nameOf(n)) + 31 * self.declaredImpls(n));
        r: long = gReg.findRequest(nameOf(n));
        if (r >= 0) {
            rq: GRequest = gReg.requestAt(r);
            acc = acc + self.fpVisit(rq.base, seen);
            for k in 0..rq.argCount { acc = acc + self.fpType(gReg.gArgAt(rq, k), seen); }
        }
        si: long = gReg.findStruct(nameOf(n));
        if (si < 0) { return acc; }
        d: StructDef = gReg.structDef(si);
        for k in 0..d.fieldCount {
            f: FieldDef = gReg.fieldAt(d, k);
            // What a value holds by value; a pointer or a slice is not released through.
            if (f.structName != NO_SYM && f.kind != Lit.Ptr && f.kind != Lit.Slice) { acc = acc + self.fpVisit(f.structName, seen); }
        }
        return acc;
    }
    // The traits the source declares for `n`, as one number, order aside.
    declaredImpls &self n:Sym -> long {
        while (self.fpImplsDone < gDeclaredImpls) {
            im: TraitImplDef = gReg.implAt(self.fpImplsDone);
            self.fpImplsDone = self.fpImplsDone + 1;
            key: long = im.structName as long;
            self.fpDecl.put(key, self.fpDecl.getOr(key, 0) + fpMix(strHash(gReg.traitMangled(im.trait))));
        }
        return self.fpDecl.getOr(n as long, 0);
    }

    // Implementations, by the type each is for, chained in the order they were registered.
    indexImpls &self -> void {
        while (self.implsIndexed < gReg.implCount()) {
            i: long = self.implsIndexed;
            self.implsIndexed = i + 1;
            owner: long = gReg.implAt(i).structName as long;
            self.implNext.push(-1);
            tail: long = self.implTail.getOr(owner, -1);
            if (tail < 0) { self.implHead.put(owner, i); } else { self.implNext.set(tail, i); }
            self.implTail.put(owner, i);
        }
    }

    // The template's impls, restated for this instance. Without them `Vec<long>` implements
    // nothing: no vtable, and no way for another template's `T: Write` bound to be met by it.
    // A block whose bounds this instance failed left its methods uncloned, and that is exactly
    // what makes the impl conditional: it is not registered either.
    // The template's impls, restated for this instance: the methods and the registration, from
    // one place. Both have to agree on the trait's spelling, and only the concrete trait gives it:
    // `VecIter<T> for Iter<&T>` at T = long is `Iter<long>`, because a borrow of a scalar is the
    // scalar. Naming the clone by substituting text into the template's own name instead produced
    // `Iter_ref_long`, which no call site would ever ask for.
    cloneImpls &self inout a:Ast base:Sym instance:Sym -> void {
        // The template's own implementations, in the order they were registered. What this adds
        // is the instance's, which is not `base`.
        self.indexImpls();
        next: long = self.implHead.getOr(base as long, -1);
        while (next >= 0) {
            i: long = next;
            next = self.implNext.get(i);
            im: TraitImplDef = gReg.implAt(i);
            // A marker trait (`MustUse`, and any other with no methods) has nothing to clone,
            // but the instance still carries the mark. Skipping it outright is what left
            // `Result<long, long>` not `MustUse` while `Result<T, E>` was, so discarding one went
            // unnoticed for every instance anybody actually wrote.
            if (im.fnCount == 0) {
                none: Vec<Sym>;
                gReg.addImpl(instance, self.concreteTrait(im.trait), none);
                continue;
            }
            at: long = gReg.findTrait(nameOf(im.trait.name));
            if (at < 0) { continue; }
            t: TraitDef = gReg.traitDef(at);
            inst: TraitImplDef = TraitImplDef { structName: instance,
                                                trait: self.concreteTrait(im.trait),
                                                firstFn: 0, fnCount: 0, carried: im.carried };
            fns: Vec<Sym>;
            all: bool = true;
            for k in 0..t.methodCount {
                m: Sym = gReg.traitMethodAt(t, k).name;
                src: Sym = implMethodName(im, m);
                dst: Sym = implMethodName(inst, m);
                fns.push(dst);
                at2: long = self.fnDefOf(a, src);
                if (at2 < 0) { all = false; }
                else if (self.meetsBounds(a.fns.get(at2))) { self.cloneFnAs(a, at2, dst); }
                else { all = false; }
            }
            // An instance that failed a block's bounds gets neither its methods nor its impl.
            if (all) { gReg.addImplAs(instance, inst.trait, fns, im.carried); }
        }
    }

    // One implementation of a template's, restated for an instance that was stamped before the
    // block's bounds could be met: a derive has since given a type argument the trait a bound
    // names (`Vec<Point>`, stamped when it was first named, and `methods Vec<T: Encode> for
    // Encode`, which needed a `Point: Encode` nobody had written yet). The checker decides the
    // bounds hold and asks (its `lateImpl`); `have[k]` says the trait's k-th method already
    // exists for the instance. The new definitions come back as their statements.
    stampImpl &self inout a:Ast base:Sym instance:Sym args:Vec<TypeRef> im:TraitImplDef have:Vec<bool> -> Vec<long> {
        out: Vec<long>;
        tat: long = gReg.findTemplate(nameOf(base));
        ti: long = gReg.findTrait(nameOf(im.trait.name));
        if (tat < 0 || ti < 0) { return out; }
        t: GTemplate = gReg.templateDef(tat);
        self.extra.clear();
        self.subst.clear();
        k: long = 0;
        while (k < t.paramCount && k < args.len()) {
            self.subst.put(nameOf(gReg.gParamAt(t, k)), args.get(k));
            k = k + 1;
        }
        self.selfBase = base;
        self.selfInstance = instance;
        self.curFp = self.fingerprint(base, args);
        self.selfArgs = args;
        td: TraitDef = gReg.traitDef(ti);
        inst: TraitImplDef = TraitImplDef { structName: instance, trait: self.concreteTrait(im.trait),
                                            firstFn: 0, fnCount: 0, carried: im.carried };
        fns: Vec<Sym>;
        for k in 0..td.methodCount {
            m: Sym = gReg.traitMethodAt(td, k).name;
            dst: Sym = implMethodName(inst, m);
            fns.push(dst);
            at: long = self.fnDefOf(a, implMethodName(im, m));
            if (at >= 0 && !have.get(k)) { self.cloneFnAs(a, at, dst); }
        }
        gReg.addImplAs(instance, inst.trait, fns, im.carried);
        self.selfBase = NO_SYM;
        self.selfInstance = NO_SYM;
        self.subst.clear();
        out.extend(self.extra);
        self.extra.clear();
        return out;
    }

    // A trait object satisfies a bound naming its own trait and no other: its vtable already
    // provides those methods. A struct satisfies one it implements, which for an instance means
    // the impl `cloneImpls` registered when the corresponding block was cloned, so an unmet bound
    // propagates outward: `BufWriter<Write>` has no `Default`, so neither does `Mutex` of it.
    // `Copy` and `Clone` are derived markers with no impl to find, and a scalar meets anything a
    // template asks of it.
    satisfies &self t:TypeRef trait:Sym -> bool {
        // `Copy` is a marker the compiler derives for anything that owns nothing, which every
        // scalar is; `Clone` is its opposite: only a value that owns something has a clone to
        // make, so `Vec<str>` gets the plain reads and not `cloneAt`.
        bare: str = lastComponentOf(nameOf(trait));
        // ...and a value that owns something is never one of them: a bitwise copy would hand two
        // owners the same resource, which is exactly what a `T: Copy` block exists to keep out.
        // Answering `true` for every type stamped `Mutex<BufWriter<Write>>.get`, whose whole body
        // is a copy of a value it would then have to release twice.
        if (bare == "Copy")  { return gReg.isCopy(t.base, t.name); }
        // `Copy` implies `Clone` (the clone of a plain value is the copy), so `Vec<long>` gets
        // `methods Vec<T: Clone> for Clone`, the deep one, rather than a clone derived field by
        // field that would share the buffer. A type that owns something is `Clone` when it has a
        // clone: written, stamped, or derivable (`cloneBlocker`). A trait object is a view with
        // no `clone` of its own to call through its table.
        if (bare == "Clone") {
            if (t.base == Lit.TraitObj) { return false; }
            if (t.base != Lit.Struct) { return gReg.isCopy(t.base, t.name); }
            return gReg.cloneBlocker(t.name).len == 0;
        }
        if (t.base == Lit.TraitObj) { return t.name == trait; }
        if (t.base == Lit.Struct) { return gReg.structImplements(nameOf(t.name), trait); }
        // A scalar can carry impls too: `methods long for Ord`. Having none is a real answer:
        // `Mutex<int>` is not `Default`, and cloning that block would emit `int.new()`.
        return gReg.structImplements(typeName(t.base), trait);
    }

    // A type argument as a diagnostic should name it: a struct by its name, a scalar by its
    // spelling.
    spellArg &self t:TypeRef -> str {
        if (t.base == Lit.Len) { return nameOf(t.name); }
        if (t.name != NO_SYM && (t.base == Lit.Struct || t.base == Lit.TraitObj)) { return nameOf(t.name); }
        return typeName(t.base);
    }

    // A trait reference under the current bindings.
    concreteTrait &self t:TraitRef -> TraitRef {
        if (t.argCount == 0) { return t; }
        args: Vec<TypeRef>;
        for k in 0..t.argCount { args.push(self.concrete(gReg.traitArgAt(t, k))); }
        return TraitRef { name: t.name, firstArg: gReg.addTraitArgs(args), argCount: args.len() };
    }

    // Whether this instance's arguments satisfy the block's bounds.
    meetsBounds &self fn:FnNode -> bool {
        for k in 0..fn.boundCount {
            b: MethodBound = gReg.boundAt(fn.firstBound + k);
            if (b.param < self.selfArgs.len()) {
                arg: TypeRef = self.selfArgs.get(b.param);
                if (!self.satisfies(arg, b.trait.name)) { return false; }
            }
        }
        return true;
    }

    cloneFn &self inout a:Ast at:long instance:Sym baseLen:long -> void {
        full: str = nameOf(a.fns.get(at).name);
        tail: str = strSlice(full, baseLen, full.len - baseLen);
        newName: Sym = internString(format("{}{}", nameOf(instance), self.substTail(tail)));
        if (self.stamped.find(nameOf(newName)).isSome()) { return; }
        self.cloneFnAs(a, at, newName);
        // A method with type parameters of its own (`map<U>` in `methods Vec<T>`): this instance's
        // copy has T bound and U still open, so it is a generic function in its turn, under its
        // own name, with the method's own parameters and bounds. A call stamps it per U.
        tat: long = gReg.findTemplate(full);
        if (tat < 0) { return; }
        t: GTemplate = gReg.templateDef(tat);
        if (t.fieldCount > 0 || t.isEnum) { return; }
        // It became a pattern: its body is what each of its own instances is cloned from.
        c: FnNode = a.fns.last();
        if (c.body == BODY_STAMP) { self.stampBody(a, a.fns.len() - 1); c = a.fns.last(); }
        a.fns.set(a.fns.len() - 1, FnNode { name: c.name, returnKind: c.returnKind, returnStruct: c.returnStruct,
                                            visibility: c.visibility, file: c.file, pkg: c.pkg,
                                            isUnsafe: c.isUnsafe, isTemplate: true, inferReturn: c.inferReturn,
                                            firstBound: t.firstBound, boundCount: t.boundCount,
                                            firstArg: c.firstArg, argCount: c.argCount, body: c.body, attrs: c.attrs });
        gReg.addTemplate(GTemplate { name: newName, firstParam: t.firstParam, paramCount: t.paramCount,
                                     firstField: t.firstField, fieldCount: 0,
                                     firstVariant: t.firstVariant, variantCount: 0,
                                     firstBound: t.firstBound, boundCount: t.boundCount,
                                     isEnum: false, visibility: t.visibility, file: t.file, pkg: t.pkg });
    }

    // The part of a method's name after its owner. For a method of a parameterized trait that is
    // `_<trait>_<args>_<method>`, and the arguments there are this template's parameters:
    // `ByOrd<T>`'s `Compare<T>` is `Compare_long` in the `long` instance. Segment by segment,
    // because a mangled name is `_`-joined and a type parameter is one whole segment.
    substTail &self tail:str -> str { return substTailBy(tail, self.subst); }

    // The body under the current bindings, as a function of its own. The one place a clone is
    // made: a method's name is its owner's instance plus its own tail, a generic function's is
    // whatever the call inferred, and nothing else differs.
    cloneFnAs &self inout a:Ast at:long newName:Sym -> void {
        fn: FnNode = a.fns.get(at);
        if (self.stamped.find(nameOf(newName)).isSome()) { return; }
        self.stamped.put(nameOf(newName), 1);
        // A package build: a dependency compiled this one against what this compile sees (it is
        // linked to), or stamped its instance and compiled no such function (it is compiled here
        // only if reached). Either way its body is stamped only when something needs it.
        // Not a `drop`: the ownership pass wraps a type's own release in glue that releases its
        // fields too, under the release's name, and does so in every compile that drops one.
        instFn: bool = gKlibMode && !strEndsWith(nameOf(newName), "_drop");
        reused: long = -1;
        if (instFn && !gInstExports.isEmpty()) { reused = instExportFor(newName, self.curFp); }
        later: bool = gKlibMode && self.mayDefer && (reused >= 0 || self.lazyInstance);
        was: long = gPos;
        if (at < self.fnPos.len() && self.fnPos.get(at) != 0) { gPos = self.fnPos.get(at); }
        // Whose code this is, for an error's "instantiated from" notes: a method's type instance,
        // or a stamped function's own instance. What the body asks for is asked on its behalf.
        owner: Sym = self.selfInstance;
        if (owner == NO_SYM) { owner = newName; }
        noteFnOwner(newName, owner);
        wasInst: Sym = gCtxInst;
        gCtxInst = owner;

        ret: TypeRef = self.concrete(TypeRef { base: fn.returnKind, name: fn.returnStruct });
        savedHints: HashMap<str, long> = map![];
        swapValues(&savedHints, &self.hintVars);
        if (!gReg.carriedOwners.isEmpty()) { self.noteHintVars(fn); }
        params: Vec<long>;
        for k in 0..fn.argCount {
            params.push(self.cloneDecl(a, a.params.get(fn.firstArg + k)));
        }
        body: long = BODY_STAMP;
        if (!later) { body = self.cloneBlock(a, fn.body); }
        first: long = a.params.len();
        a.params.extend(params);
        if (later) { self.noteLater(a.fns.len(), at, owner); }
        a.fns.push(FnNode { name: newName, returnKind: ret.base, returnStruct: ret.name,
                            visibility: fn.visibility, file: fn.file, pkg: fn.pkg,
                            isUnsafe: fn.isUnsafe, isTemplate: false, inferReturn: fn.inferReturn,
                            firstBound: 0, boundCount: 0,
                            firstArg: first, argCount: params.len(), body: body, attrs: fn.attrs });
        self.extra.push(a.addStmt(StmtKind.FunctionDef, a.fns.len() - 1));
        // What this instance was compiled against, and the dependency that compiled it already.
        if (instFn) {
            gInstanceFp.put(nameOf(newName), self.curFp);
            if (reused >= 0) { self.reuseOf(a, a.fns.len() - 1, reused); }
        }
        swapValues(&savedHints, &self.hintVars);
        gPos = was;
        gCtxInst = wasInst;
    }

    // The bounds on each type parameter of the function being cloned (a generic function's own,
    // or its methods block's, whose parameters are the type's), each as a run of trait names.
    noteHintVars &self fn:FnNode -> void {
        if (fn.boundCount == 0) { return; }
        tat: long = gReg.findTemplate(nameOf(fn.name));
        if (tat < 0 && self.selfBase != NO_SYM) { tat = gReg.findTemplate(nameOf(self.selfBase)); }
        if (tat < 0) { return; }
        t: GTemplate = gReg.templateDef(tat);
        for p in 0..t.paramCount {
            start: long = gHintTraits.len();
            for k in 0..fn.boundCount {
                b: MethodBound = gReg.boundAt(fn.firstBound + k);
                if (b.param == p) { gHintTraits.push(b.trait.name); }
            }
            if (gHintTraits.len() == start) { continue; }
            gHintTraits.push(NO_SYM);
            self.hintVars.put(nameOf(gReg.gParamAt(t, p)), start);
        }
    }

    cloneDecl &self inout a:Ast at:long -> long {
        d: VarDeclNode = a.decls.get(at);
        t: TypeRef = self.concrete(TypeRef { base: d.kind, name: d.structName });
        e: TypeRef = self.concrete(TypeRef { base: d.elemKind, name: d.elemStruct });
        // `inout` on a struct is the borrow representation: the parser applies that where the
        // type is written, but a template's `inout t:T` had no type to apply it to until now. A
        // slice stays a slice: it is already a fat pointer, and `inout` only says the callee may
        // write through it. Without this the stamped `take<Vec<long>>` took its parameter by
        // value, and the `replace(t, fresh)` in its body was refused for not lending.
        if (d.conv == Conv.Inout && t.base == Lit.Struct) { t = TypeRef { base: Lit.Ref, name: t.name }; }
        a.decls.push(VarDeclNode { name: d.name, kind: t.base, structName: t.name,
                                   isArray: d.isArray, count: self.concreteCount(d.count), conv: d.conv,
                                   isVariadic: d.isVariadic, elemKind: e.base,
                                   elemStruct: e.name, init: self.cloneExpr(a, d.init) });
        return a.decls.len() - 1;
    }

    // ─── statements ──────────────────────────────────────────────────────────

    cloneBlock &self inout a:Ast at:long -> long {
        b: Block = a.blocks.get(at);
        ids: Vec<long>;
        for k in 0..b.stmtCount {
            ids.push(self.cloneStmt(a, a.stmtRuns.get(b.firstStmt + k)));
        }
        return a.addBlock(ids);
    }

    // A clone stands where the statement it copies does, and so does anything said while copying.
    cloneStmt &self inout a:Ast at:long -> long {
        was: long = a.enterStmt(at);
        id: long = self.cloneStmtHere(a, at);
        gPos = was;
        return id;
    }
    cloneStmtHere &self inout a:Ast at:long -> long {
        s: Stmt = a.stmts.get(at);
        if (s.kind == StmtKind.VarDecl) {
            return a.addStmt(StmtKind.VarDecl, self.cloneDecl(a, s.at));
        }
        if (s.kind == StmtKind.If)     { return a.addStmt(StmtKind.If, self.cloneIf(a, s.at)); }
        if (s.kind == StmtKind.While) {
            w: WhileNode = a.whiles.get(s.at);
            // The step is a block (`for` puts the increment in one so `continue` runs it) not
            // the single statement its name suggests.
            step: long = NO_STMT;
            if (w.step != NO_STMT) { step = self.cloneBlock(a, w.step); }
            cond: NodeId = self.cloneExpr(a, w.cond);
            body: long = self.cloneBlock(a, w.body);
            a.whiles.push(WhileNode { cond: cond, body: body, step: step });
            return a.addStmt(StmtKind.While, a.whiles.len() - 1);
        }
        if (s.kind == StmtKind.Loop || s.kind == StmtKind.Unsafe || s.kind == StmtKind.Block) {
            bs: BlockStmtNode = a.blockStmts.get(s.at);
            body: long = self.cloneBlock(a, bs.body);
            a.blockStmts.push(BlockStmtNode { body: body });
            return a.addStmt(s.kind, a.blockStmts.len() - 1);
        }
        if (s.kind == StmtKind.With) {
            w: WithNode = a.withs.get(s.at);
            body: long = self.cloneBlock(a, w.body);
            a.withs.push(WithNode { name: w.name, body: body });
            return a.addStmt(StmtKind.With, a.withs.len() - 1);
        }
        if (s.kind == StmtKind.Return) {
            r: ReturnNode = a.returns.get(s.at);
            a.returns.push(ReturnNode { value: self.cloneExpr(a, r.value) });
            return a.addStmt(StmtKind.Return, a.returns.len() - 1);
        }
        if (s.kind == StmtKind.Expr || s.kind == StmtKind.Call) {
            e: ExprStmtNode = a.exprStmts.get(s.at);
            a.exprStmts.push(ExprStmtNode { value: self.cloneExpr(a, e.value) });
            return a.addStmt(s.kind, a.exprStmts.len() - 1);
        }
        if (s.kind == StmtKind.Destructure) {
            d: DestructureNode = a.destructures.get(s.at);
            names: Vec<Sym>;
            for k in 0..d.nameCount { names.push(a.names.get(d.firstName + k)); }
            value: NodeId = self.cloneExpr(a, d.value);
            firstName: long = a.names.len();
            a.names.extend(names);
            a.destructures.push(DestructureNode { firstName: firstName, nameCount: names.len(),
                                                  value: value });
            return a.addStmt(StmtKind.Destructure, a.destructures.len() - 1);
        }
        if (s.kind == StmtKind.Match)  { return a.addStmt(StmtKind.Match, self.cloneMatch(a, s.at)); }
        if (s.kind == StmtKind.Asm)    { return a.addStmt(StmtKind.Asm, self.cloneAsm(a, s.at)); }
        // Break, Continue, StructDecl and a nested FunctionDef carry nothing that refers into the
        // arena, so the statement is its own copy.
        return a.addStmt(s.kind, s.at);
    }

    cloneIf &self inout a:Ast at:long -> long {
        n: IfNode = a.ifs.get(at);
        cond: NodeId = self.cloneExpr(a, n.cond);
        body: long = self.cloneBlock(a, n.body);
        chain: long = -1;
        if (n.elseIf >= 0) { chain = self.cloneIf(a, n.elseIf); }
        a.ifs.push(IfNode { cond: cond, body: body, elseIf: chain });
        return a.ifs.len() - 1;
    }

    cloneMatch &self inout a:Ast at:long -> long {
        m: MatchNode = a.matches.get(at);
        arms: Vec<ArmNode>;
        for k in 0..m.armCount {
            arm: ArmNode = a.arms.get(m.firstArm + k);
            binds: Vec<Sym>;
            for b in 0..arm.bindCount { binds.push(a.names.get(arm.firstBind + b)); }
            body: long = self.cloneBlock(a, arm.body);
            firstBind: long = a.names.len();
            a.names.extend(binds);
            arms.push(ArmNode { variant: arm.variant, test: self.cloneExpr(a, arm.test),
                                firstBind: firstBind, bindCount: binds.len(), body: body });
        }
        firstArm: long = a.arms.len();
        a.arms.extend(arms);
        a.matches.push(MatchNode { scrutinee: m.scrutinee, firstArm: firstArm,
                                   armCount: arms.len() });
        return a.matches.len() - 1;
    }

    cloneAsm &self inout a:Ast at:long -> long {
        n: AsmNode = a.asms.get(at);
        pieces: Vec<AsmPiece>;
        for k in 0..n.pieceCount {
            p: AsmPiece = a.asmPieces.get(n.firstPiece + k);
            pieces.push(AsmPiece { kind: p.kind, reg: p.reg, name: p.name,
                                   value: self.cloneExpr(a, p.value), text: p.text });
        }
        first: long = a.asmPieces.len();
        a.asmPieces.extend(pieces);
        a.asms.push(AsmNode { firstPiece: first, pieceCount: pieces.len(), noReturn: n.noReturn });
        return a.asms.len() - 1;
    }

    // ─── expressions ─────────────────────────────────────────────────────────

    cloneExpr &self inout a:Ast id:NodeId -> NodeId {
        if (id < 0) { return id; }
        e: Expr = a.exprs.get(id);
        // A length parameter named in a body is its value in this instance: a `long` literal,
        // which is all the checker, the evaluator and the back end ever see of it.
        if (e.op == Op.Lvalue) {
            match e.payload {
                Name(n) {
                    hit: Option<TypeRef> = self.subst.find(nameOf(n));
                    match hit {
                        Some(b) {
                            if (b.base == Lit.Len) {
                                a.exprs.push(Expr { op: Op.Literal, left: NO_NODE, right: NO_NODE, kind: Lit.Long,
                                                    structName: NO_SYM, isParen: e.isParen,
                                                    payload: Payload.Num(lengthValue(b)) });
                                return a.exprs.len() - 1;
                            }
                        }
                        None { }
                    }
                }
                _ { }
            }
        }
        t: TypeRef = self.concrete(TypeRef { base: e.kind, name: e.structName });
        left: NodeId = self.cloneExpr(a, e.left);
        right: NodeId = self.cloneExpr(a, e.right);
        payload: Payload = self.clonePayload(a, e.payload);
        a.exprs.push(Expr { op: e.op, left: left, right: right, kind: t.base,
                            structName: t.name, isParen: e.isParen, payload: payload });
        return a.exprs.len() - 1;
    }

    clonePayload &self inout a:Ast p:Payload -> Payload {
        match p {
            Sub(inner) { return Payload.Sub(self.cloneExpr(a, inner)); }
            Index(ix) {
                n: IndexNode = a.indexes.get(ix);
                base: NodeId = self.cloneExpr(a, n.base);
                index: NodeId = self.cloneExpr(a, n.index);
                lo: NodeId = self.cloneExpr(a, n.sliceStart);
                hi: NodeId = self.cloneExpr(a, n.sliceEnd);
                a.indexes.push(IndexNode { name: n.name, base: base, index: index,
                                           whole: n.whole, rawPointerBase: n.rawPointerBase,
                                           sliceStart: lo, sliceEnd: hi, at: n.at });
                return Payload.Index(a.indexes.len() - 1);
            }
            Call(c) {
                n: CallNode = a.calls.get(c);
                recv: NodeId = self.cloneExpr(a, n.receiver);
                args: Vec<NodeId>;
                for k in 0..n.argCount {
                    args.push(self.cloneExpr(a, a.argAt(n, k)));
                }
                first: long = a.args.len();
                a.args.extend(args);
                // The signature an indirect call goes through is a type like any other in a
                // template (`f(v)` where `f: fn(T)->U`) so the clone gets the concrete one.
                key: Sym = n.sigKey;
                if (key != NO_SYM) { key = self.concrete(TypeRef { base: Lit.Fn, name: key }).name; }
                a.calls.push(CallNode { name: self.substCallName(n.name), receiver: recv,
                                        callee: self.cloneExpr(a, n.callee),
                                        firstArg: first, argCount: args.len(), slot: n.slot,
                                        sigKey: key });
                // `x.m()` on a `T: Show`: the traits T was bound by, for the checker.
                if (!self.hintVars.isEmpty() && n.receiver != NO_NODE) {
                    re: Expr = a.exprs.get(n.receiver);
                    if ((re.kind == Lit.TypeVar || re.kind == Lit.Ref) && re.structName != NO_SYM) {
                        hv: Option<long> = self.hintVars.find(nameOf(re.structName));
                        match hv { Some(h) { gCallHints.put(a.calls.len() - 1, h); } None { } }
                    }
                }
                return Payload.Call(a.calls.len() - 1);
            }
            Field(f) {
                n: FieldNode = a.fields.get(f);
                a.fields.push(FieldNode { base: self.cloneExpr(a, n.base), name: n.name });
                return Payload.Field(a.fields.len() - 1);
            }
            Lit(l) {
                n: LitNode = a.lits.get(l);
                inits: Vec<InitNode>;
                for k in 0..n.initCount {
                    ini: InitNode = a.inits.get(n.firstInit + k);
                    inits.push(InitNode { name: ini.name, value: self.cloneExpr(a, ini.value) });
                }
                first: long = a.inits.len();
                a.inits.extend(inits);
                a.lits.push(LitNode { typeName: self.substTypeName(n.typeName),
                                      firstInit: first, initCount: inits.len(),
                                      rest: self.cloneExpr(a, n.rest) });
                if (n.typeName == self.selfBase && n.typeName != NO_SYM) { gSelfLits.put(a.lits.len() - 1, true); }
                return Payload.Lit(a.lits.len() - 1);
            }
            None    { return Payload.None; }
            Num(v)  { return Payload.Num(v); }
            Text(t) { return Payload.Text(t); }
            Image(i) { return Payload.Image(i); }     // bytes are concrete already
            // `T.new()`: a type parameter standing where a type is named, not a variable. The
            // parser could only record it as a name; here it becomes the type T turned out to be,
            // after which the checker resolves an ordinary static call to it.
            Name(n) {
                hit: Option<TypeRef> = self.subst.find(nameOf(n));
                match hit {
                    Some(b) { return Payload.Name(intern(typeMangleName(b.base, b.name))); }
                    None { }
                }
                return Payload.Name(n);
            }
        }
        return Payload.None;
    }

    // A struct literal inside a template names the template: `Vec { ... }` in `methods Vec<T>`
    // means the instance being stamped. Anything else is already concrete.
    substTypeName &self n:Sym -> Sym {
        if (n == NO_SYM) { return n; }
        bound: TypeRef = self.concreteNamed(n);
        if (bound.base == Lit.Struct) { return bound.name; }
        return n;
    }

    // `Mutex_W` inside `BufWriter<W>`'s methods names an instance of another template whose
    // argument is this one's parameter. Rebuilt under the current bindings, and asked for, since
    // `Mutex<FileOut>` is a type nobody has stamped and the run loop reads this table as it goes.
    substInstance &self n:Sym -> Sym {
        at: long = gReg.findRequest(nameOf(n));
        if (at < 0) { return n; }
        r: GRequest = gReg.requestAt(at);
        if (!gReg.isPatternRequest(r)) { return n; }
        args: Vec<TypeRef>;
        s: String;
        s.pushStr(nameOf(r.base));
        for k in 0..r.argCount {
            c: TypeRef = self.concrete(gReg.gArgAt(r, k));
            if (c.base == Lit.TypeVar) { return n; }        // an outer stamp still owes a binding
            args.push(c);
            s.push('_');
            s.pushStr(typeMangleName(c.base, c.name));
        }
        inst: Sym = internString(s);
        gReg.request(r.base, inst, args);
        return inst;
    }

    // `(T, long)` inside a template is the tuple of what T is bound to. A tuple is named by its
    // elements, so the instance is that name rebuilt under the bindings and registered (once:
    // registering is idempotent), the way `substInstance` rebuilds `Vec_T`.
    substTuple &self n:Sym -> Sym {
        elems: Vec<TypeRef> = tupleElems(n);
        changed: bool = false;
        for k in 0..elems.len() {
            e: TypeRef = elems.get(k);
            c: TypeRef = self.concrete(e);
            if (c.base == Lit.TypeVar) { return n; }        // an outer stamp still owes a binding
            if (c.base != e.base || c.name != e.name) { changed = true; elems.set(k, c); }
        }
        if (!changed) { return n; }
        return registerTuple(elems);
    }

    // `T.new()` inside a template is a static call on whatever T is. The parser recorded it as
    // `T_new`, so the leading parameter name is what has to move.
    substCallName &self n:Sym -> Sym {
        if (n == NO_SYM) { return n; }
        s: str = nameOf(n);
        cut: long = 0;
        while (cut < s.len && charAt(s, cut) != '_') { cut = cut + 1; }
        if (cut >= s.len) { return n; }
        head: str = strSlice(s, 0, cut);
        hit: Option<TypeRef> = self.subst.find(head);
        match hit {
            Some(bound) {
                return internString(format("{}{}", typeMangleName(bound.base, bound.name),
                                           strSlice(s, cut, s.len - cut)));
            }
            None { }
        }
        if (head == nameOf(self.selfBase)) {
            return internString(format("{}{}", nameOf(self.selfInstance),
                                       strSlice(s, cut, s.len - cut)));
        }
        return n;
    }
}

// `Mono.substTail` under any bindings: what the checker names an instance's method by before it is
// stamped (`Checker.instantiateOwner`), which has to be exactly the clone's name.
pub substTailBy tail:str subst:&HashMap<str, TypeRef> -> str {
    out: String;
    start: long = 0;
    i: long = 0;
    while (i <= tail.len) {
        if (i == tail.len || charAt(tail, i) == '_') {
            seg: str = strSlice(tail, start, i - start);
            hit: Option<TypeRef> = subst.find(seg);
            match hit {
                Some(b) { out.pushStr(typeMangleName(b.base, b.name)); }
                None    { out.pushStr(seg); }
            }
            if (i < tail.len) { out.push('_'); }
            start = i + 1;
        }
        i = i + 1;
    }
    return keepString(out);
}
