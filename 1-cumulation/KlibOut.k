// Writing a package's `.klib` metadata: what its compile decided, gathered from the phases that
// decided it, and the package's own modules as their parser left them (`KlibTree`), as the
// dependents will read them (`Klib`).
#include <{Klib, KlibTree, Scanner, Module}>
#include <support::compiler>
#include <parse::{ast, registry, upstream}>
#include <transform::{check, guard, eval, facts}>
#include <codegen::{asm, lower, irpack}>
#include <pre::{Preprocessor, PackageMap}>
#include <stdlib::{encode, file, hash128, path, pathbuf, map, option, result, string, vec}>

// Every function this package's source defines: its parameters as inference left them, its
// return as settled, whether it diverges, and what the guard found it writes. After the guard,
// which is the last of the phases that decide any of it. Filed by the function's index, which is
// how a module's section lists them.
pub collectFnFacts inout a:Ast inout ck:Checker inout cg:ConstGuard -> void {
    gOutFnFactAt.clear();
    for at in 0..gParsedCount { gOutFnFactAt.push(-1); }
    for at in 0..gParsedCount {
        if (!isOwnSourceFn(a, at)) { continue; }
        f: FnNode = a.fns.get(at);
        if (f.body < 0) { continue; }
        gOutFnFactAt.set(at, fnFactHere(a, &ck, &cg, at));
    }
    // The instance functions this compile checked, by name: the ones the emitter goes on to
    // write are exported, and their facts go with them (INSTFNS).
    for at in gParsedCount..a.fns.len() {
        f: FnNode = a.fns.get(at);
        if (f.isTemplate || f.body < 0 || isExternFn(at) || isUnchecked(at)) { continue; }
        if (!gInstanceFp.has(nameOf(f.name))) { continue; }
        gOutInstFact.put(nameOf(f.name), fnFactHere(a, &ck, &cg, at));
    }
}

// What this compile decided about function `at`, into `gOutFacts`; its index there.
local fnFactHere inout a:Ast inout ck:Checker inout cg:ConstGuard at:long -> long {
    f: FnNode = a.fns.get(at);
    ps: Vec<ParamFact>;
    for k in 0..f.argCount {
        p: VarDeclNode = a.paramAt(f, k);
        ps.push(ParamFact { conv: p.conv, kind: p.kind });
    }
    return gOutFacts.addFn(FnFact { divergent: ck.isDivergingFn(f.name), writes: cg.writesOf(at),
                                    retKind: f.returnKind, retStruct: f.returnStruct,
                                    firstParam: 0, paramCount: 0, firstDep: 0, depCount: 0 },
                           ps, cg.depsOf(at));
}

// Every global this package declares, as the evaluator left it -- a scalar, an image, zero, or
// built at startup -- with the images copied across and renumbered, and what the startup
// initializers (this package's, and those beneath it) may write. After `foldGlobals`.
pub collectGlobalFacts inout a:Ast page:long inout ev:Evaluator -> void {
    remap: HashMap<long, long>;
    n: long = a.blockLen(page);
    for k in 0..n {
        st: Stmt = a.stmtAt(page, k);
        if (st.kind != StmtKind.VarDecl) { continue; }
        d: VarDeclNode = a.decls.get(st.at);
        gi: long = gReg.findGlobal(nameOf(d.name));
        if (gi < 0 || gReg.globalDef(gi).pkg != gThisPkg) { continue; }
        state: GlobalState = GlobalState.Startup;
        value: long = 0;
        image: long = -1;
        if (d.init == NO_NODE) { state = GlobalState.Zero; }
        else {
            e: Expr = a.expr(d.init);
            if (e.op == Op.Literal) {
                match e.payload { Num(v) { state = GlobalState.Scalar; value = v; } _ { } }
            } else if (e.op == Op.Image) {
                match e.payload { Image(im) { state = GlobalState.Image; image = copyImage(a, im, &remap); } _ { } }
            }
        }
        gOutFacts.addGlobal(GlobalFact { name: d.name, state: state, value: value, image: image });
    }
    if (ev.poison.all || gFacts.poisonAll) { gOutFacts.poisonAll = true; }
    for g in ev.poison.order { gOutFacts.addPoison(g); }
    for p in gFacts.poison { gOutFacts.addPoison(p); }
}

// Image `im` of the tree into the facts, and every block it points at, each once.
local copyImage inout a:Ast im:long inout remap:HashMap<long, long> -> long {
    hit: Option<long> = remap.find(im);
    match hit { Some(i) { return i; } None { } }
    out: long = gOutFacts.images.len();
    remap.put(im, out);
    node: ImageNode = a.images.get(im);
    // Reserve the slot first: a block reached from inside its own contents names this index.
    gOutFacts.images.push(ImgFact { firstByte: 0, byteCount: 0, firstReloc: 0, relocCount: 0, isBlock: node.isBlock });
    relocs: Vec<RelocFact>;
    for k in 0..node.relocCount {
        r: RelocNode = a.relocs.get(node.firstReloc + k);
        target: long = -1;
        if (r.kind == RelocKind.Block) { target = copyImage(a, r.image, remap); }
        conc: Sym = NO_SYM;
        tr: Sym = NO_SYM;
        if (r.kind == RelocKind.Vtable) {
            ph: Option<long> = gVtablePairs.find(nameOf(r.target));
            match ph {
                Some(pi) { conc = gVtableConcrete.get(pi); tr = gVtableTrait.get(pi); }
                None { failStr(format("internal: the vtable '{}' in a folded global has no recorded type", nameOf(r.target))); }
            }
        }
        relocs.push(RelocFact { offset: r.offset, kind: r.kind, target: r.target, image: target,
                                delta: r.delta, concrete: conc, trait: tr });
    }
    firstByte: long = gOutFacts.bytes.len();
    for k in 0..node.byteCount { gOutFacts.bytes.push(a.imageBytes.get(node.firstByte + k)); }
    firstReloc: long = gOutFacts.relocs.len();
    gOutFacts.relocs.extend(relocs);
    gOutFacts.images.set(out, ImgFact { firstByte: firstByte, byteCount: node.byteCount,
                                        firstReloc: firstReloc, relocCount: relocs.len(),
                                        isBlock: node.isBlock });
    return out;
}


// The metadata member, written to `path`: the text header, then the body its `body` line gives
// the length and hash of. `deps` are the direct dependencies, each with the key of the build
// loaded here.
pub writeKlibMeta path:str inout sc:Scanner compilerId:str root:str deps:Vec<str> hasMain:bool -> void {
    // The files this compile read for its own package, and the dependencies it was built
    // against: the key is computed from exactly these.
    sources: Vec<str>;
    extras: Vec<str>;
    for scanned in sc.modules {
        if (!(scanned.package == nameOf(gThisPkg))) { continue; }
        sources.push(scanned.path);
        if (!(dirOf(scanned.path) == root)) { extras.push(scanned.path); }
    }
    loaded: Vec<KlibDep>;
    for dep in deps {
        at: long = klibIndex(dep);
        if (at >= 0) { loaded.push(KlibDep { name: dep, key: gKlibs.get(at).key }); }
    }
    manifest: String = joinPath(root, MANIFEST);
    if (root.len == 0) { manifest = stringOf(MANIFEST); }
    key: String;
    unsafe { key = klibKey(compilerId, nameOf(gThisPkg), manifest.view(), sources, loaded); }

    // The body: every chunk but the strings, which are known only once everything else that
    // names one has been written, and go first.
    rest: Encoder;
    modules: Encoder;
    dir: Vec<ModRec>;
    for om in gOutModules {
        mod: Module = sc.at(om.mod);
        incs: Vec<str>;
        for j in 0..mod.importCount { incs.push(sc.at(sc.importAt(mod, j)).path); }
        start: long = modules.len();
        writeModuleSection(&modules, om);
        dir.push(ModRec { path: mod.path, pkg: mod.package, includes: incs,
                          hasMacro: moduleDeclaresMacro(mod.source), at: start, len: modules.len() - start });
    }
    chunk: Encoder;
    gExportedSyms.encode(chunk);
    putEncoded(&rest, CHUNK_EXPORTS, &chunk);
    // The generic struct instances this compile stamped, with every method checked: a dependent
    // that stamps one again compiles only the methods it reaches.
    stamped: Vec<str>;
    for k in 0..gReg.requestCount() {
        rq: GRequest = gReg.requestAt(k);
        if (gReg.isPatternRequest(rq) || !gReg.hasStruct(nameOf(rq.instance))) { continue; }
        if (gKnownInstances.has(nameOf(rq.instance))) { continue; }
        stamped.push(nameOf(rq.instance));
    }
    stamped.encode(chunk);
    putEncoded(&rest, CHUNK_STAMPED, &chunk);
    gEmittedLocal.encode(chunk);
    putEncoded(&rest, CHUNK_INSTANCES, &chunk);
    gEmittedVtables.encode(chunk);
    putEncoded(&rest, CHUNK_VTABLES, &chunk);
    // The generic instance functions this package compiled and exports: each one's name, the
    // alias it is linked by, what it was compiled against, and what compiling it decided.
    chunk.putLen(gExportedInst.len());
    for k in 0..gExportedInst.len() {
        n: Sym = gExportedInst.get(k);
        fi: long = gOutInstFact.getOr(nameOf(n), -1);
        if (fi < 0) { failStr(format("internal: the instance function '{}' was compiled and has no facts", nameOf(n))); }
        n.encode(chunk);
        alias: Sym = intern(instanceAlias(nameOf(n)));
        alias.encode(chunk);
        fp: long = gInstanceFp.getOr(nameOf(n), 0);
        fp.encode(chunk);
        putFnFact(&chunk, fi);
    }
    putEncoded(&rest, CHUNK_INSTFNS, &chunk);
    // The IR of what this package exports that a dependent's inliner could copy.
    writeShipChunk(&chunk);
    putEncoded(&rest, CHUNK_IR, &chunk);
    gOutFacts.poisonAll.encode(chunk);
    gOutFacts.poison.encode(chunk);
    putEncoded(&rest, CHUNK_POISON, &chunk);
    // The folded globals' images: each one's bytes in one piece, then where its pointers are.
    chunk.putLen(gOutFacts.images.len());
    for k in 0..gOutFacts.images.len() {
        im: ImgFact = gOutFacts.images.get(k);
        im.isBlock.encode(chunk);
        unsafe { chunk.putBytes(gOutFacts.bytes.buf.ptr[im.firstByte..im.firstByte + im.byteCount]); }
        chunk.putLen(im.relocCount);
        for j in 0..im.relocCount { r: RelocFact = gOutFacts.relocs.get(im.firstReloc + j); r.encode(chunk); }
    }
    putEncoded(&rest, CHUNK_IMAGES, &chunk);
    dir.encode(chunk);
    putEncoded(&rest, CHUNK_MODDIR, &chunk);
    putEncoded(&rest, CHUNK_MODULES, &modules);

    body: Encoder;
    strings: Encoder;
    strings.putLen(gSymTable.len());
    for s in gSymTable { strings.putLen(nameOf(s).len); }
    for s in gSymTable { strings.putRaw(nameOf(s) as [u8]); }
    putEncoded(&body, CHUNK_STRINGS, &strings);
    unsafe { body.putRaw(rest.view()); }

    s: String;
    s.pushStr(KLIB_FORMAT);
    s.push('\n');
    s.pushStr("package ");
    putText(&s, nameOf(gThisPkg));
    s.pushStr("\nkey ");
    s.pushString(key);
    s.push('\n');
    for d in loaded {
        s.pushStr("dep ");
        putText(&s, d.name);
        s.push(' ');
        s.pushStr(d.key);
        s.push('\n');
    }
    for e in extras { s.pushStr("extra "); putText(&s, e); s.push('\n'); }
    s.pushStr("init ");
    init: str = nameOf(initFunctionName());
    if (gExportedSymsHas(fnLabel(init))) { putText(&s, fnLabel(init)); } else { s.push('-'); }
    s.pushStr("\nentry ");
    if (hasMain) { s.push('1'); } else { s.push('0'); }
    s.pushStr("\nbody ");
    s.pushLong(body.len());
    s.push(' ');
    h: Hash128;
    unsafe { h = hash128(body.view()); }
    s.pushString(h.hex());
    s.push('\n');
    unsafe {
        b: [u8] = body.view();
        s.pushStr(b as str);
    }
    v: str = "";
    unsafe { v = s.view(); }
    r: Result<long, long> = writeFileStr(path, v);
    match r {
        Ok(_)  { }
        Err(e) { failStr(format("could not write {} (errno {})", path, e)); }
    }
}

// A chunk from what `src` holds, which is emptied for the next one.
local putEncoded inout out:Encoder tag:long inout src:Encoder -> void {
    unsafe { putChunk(out, tag, src.view()); }
    src.out.clear();
}

local gExportedSymsHas label:str -> bool {
    for s in gExportedSyms {
        if (s == label) { return true; }
    }
    return false;
}
