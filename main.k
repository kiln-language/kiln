// The self-hosted Kiln compiler.
//
//   kilnc foo.k                 compile
//   kilnc foo.k --emit=<stage>  dump one intermediate representation and stop
#include <stdlib::{chars, file, io, result, string, time, vec}>
#include <support::compiler>
#include <parse::{diag, upstream, regops, treecodec, astdump, ast, parser}>
#include <cumul::{Module, Scanner, Klib, KlibOut, KlibTree, Build}>
#include <transform::{facts, check, eval, guard, mono}>
#include <pre::Preprocessor>
#include <codegen::{asm, lower, opt, flow, relayout, irdump, llvm, ir, irpack}>
#include <lex::{lexer, token}>

local USAGE: str = "usage: kilnc <file.k> [-o out.s] | kilnc build [root] [-o exe] | kilnc --klib <modules...> [--extern pkg=path.klib]... [--meta M] [--compiler-id H] -o out.s; [--emit=pre|tokens|ast|typed|ir|llvm] [--lib] [--use syms] [--time-phases] [--trace-fold] [--trace-opt] [--no-flow] [--no-thread] [--no-cse] [--fold-steps=N] [--fold-heap=MiB]";

// The number after `--flag=`, which must be one, and positive.
local flagNumber flag:str at:long -> long {
    got: Option<long> = parseLong(strSlice(flag, at, flag.len - at));
    match got { Some(n) { if (n > 0) { return n; } } None { } }
    failStr(format("'{}' needs a positive number", flag));
    return 0;
}

// A stamped generic function can call another, so instantiation is a fixpoint. The bound is a
// guard against a template that instantiates itself without end, not a real depth: three rounds
// already cover anything the stdlib has.
local MAX_STAMP_ROUNDS: long = 16;

// Time spent reading modules out of `.klib`s, for `--time-phases`.
local var gLoadUs: long = 0;


// Everything between parsing and lowering: stamp every generic instance the program asked for,
// type it, and repeat while the typing asks for more. A generic function is instantiated by a
// call, so the checker is what discovers one, and a stamped body may call another. Each round
// checks only the definitions the previous one added, since checking a body rewrites it and must
// not run over the same body twice. Returns the page, which grows as definitions are added.
//
// One function because every entry point needs all of it: a `--emit=ir` dump that skipped the
// stamping would be typing a program that does not exist.
local middleEnd inout a:Ast page:long -> long {
    gPos = 0;                     // each pass below says where it is as it walks
    phaseStart();
    gPhase = "monomorphizing";
    mo: Mono;
    page = mo.run(a, page);
    phaseEnd("monomorphize");
    gPhase = "type-checking";
    ck: Checker;
    bad: long = ck.run(a, page);
    // The checker goes on past an error to the next function (`checkGuarded`); a round that met
    // any ends the compile here, before anything reads a body an error cut short.
    stopIfErrors();
    phaseEnd("check");
    rounds: long = 0;
    // A function held back for a macro not yet runnable is another reason for a round: the
    // macro's callees get checked (and stamped) by the round, and the holder is retried. A
    // round that stamps nothing and frees nothing is stuck, and says on what.
    // So is an implementation a derive stubbed and its macro has yet to write (see check.k's
    // derives), and a method stamped for one that waits for its types to be laid out.
    while ((ck.wanted.len() > 0 || ck.wantedClones.len() > 0 || ck.deferredCount() > 0 || mo.pendingRequests()
            || ck.deriveWork() > 0) && rounds < MAX_STAMP_ROUNDS) {
        heldBefore: long = ck.deferredCount();
        derivedBefore: long = ck.derivesRun;
        checkedBefore: long = ck.fnDone.len();
        stamping: bool = ck.wanted.len() > 0 || ck.wantedClones.len() > 0 || mo.pendingRequests() || ck.lateFns.len() > 0;
        pending: Vec<FnRequest> = ck.takeWanted();
        clones: Vec<Sym> = ck.takeWantedClones();
        was: long = a.blockLen(page);
        page = mo.stampFunctions(a, page, pending);
        page = mo.deriveClones(a, page, clones);
        gPhase = "type-checking";
        bad = ck.runFrom(a, page, was);
        stopIfErrors();
        if (!stamping && ck.deferredCount() >= heldBefore && heldBefore > 0 && ck.wanted.len() == 0) {
            failStr(format("a macro cannot be prepared: {}", ck.deferReason));
        }
        if (!stamping && heldBefore == 0 && ck.derivesRun == derivedBefore && ck.fnDone.len() == checkedBefore
            && ck.deriveQ.len() > 0 && ck.wanted.len() == 0 && ck.deferredCount() == 0) {
            failStr(format("a derive cannot be prepared: {}", ck.deferReason));
        }
        rounds = rounds + 1;
    }
    if (ck.deriveWork() > 0) { failStr(format("the derives did not settle in {} rounds: {}", MAX_STAMP_ROUNDS, ck.deferReason)); }
    phaseEnd("stamp/check rounds");
    if (bad > 0) { eprintln("{} type errors", bad); }
    // Every non-void function ends on a return, or on something that never comes back. After the
    // rounds, not inside one: whether a callee returns can depend on a generic stamped later.
    gPos = 0;
    gPhase = "checking the whole program";
    ck.checkReturns(&a);
    // An implementation hands its parameters over the way its trait says. Also after the rounds:
    // an inferred convention is not settled until the last one has run.
    ck.checkImplConventions(&a);
    // A safe function may not hand back a view of the frame it is leaving.
    ck.checkReturnedViews(&a);
    // A closure may not assign to a capture it holds by value.
    ck.checkCapturedWrites(&a);
    phaseEnd("settled-program checks");
    // A `const` global is never written: every use in the program is held to that first.
    gPos = 0;
    gPhase = "holding globals to immutability";
    cg: ConstGuard;
    cg.run(a, page);
    gCtxFn = NO_SYM;
    gCtxInst = NO_SYM;
    stopIfErrors();
    phaseEnd("const guard");
    // A package build writes down what the phases so far decided about its functions, for the
    // dependents that will not run them over these bodies again.
    if (gKlibMode) { collectFnFacts(&a, &ck, &cg); }
    // Then what can be computed now, is: a global whose initializer folds becomes a constant in
    // `.data` rather than a store at every program start.
    gPhase = "folding globals";
    ev: Evaluator;
    ev.foldGlobals(a, page);
    if (gKlibMode) { collectGlobalFacts(&a, page, &ev); }
    gPos = 0;
    phaseEnd("fold globals");
    return page;
}

// A dependency's closure written without `-> T` returns what its own compile settled on, and a
// caller here is typed against that before anything else is.
local applyExternReturns inout a:Ast -> void {
    for i in 0..a.fns.len() {
        f: FnNode = a.fns.get(i);
        if (isExternFn(i) && f.inferReturn) {
            fi: long = fnFactOf(i);
            if (fi >= 0) {
                fact: FnFact = gFacts.fns.get(fi);
                f.returnKind = fact.retKind;
                f.returnStruct = fact.retStruct;
                f.inferReturn = false;
                a.fns.set(i, f);
            }
        }
    }
}

main args: ...str -> int {
    installDiagnostics();
    // `kilnc build`: the package build driver, which runs this same compiler per package.
    if (args.len > 1 && args[1] == "build") { return runBuild(args); }

    input: str = "";
    inputs: Vec<str>;
    output: str = "";

    emit:  str = "";
    verifyOps: bool = false;
    klibVerify: bool = false;
    // A package build: the package's modules are the inputs, its dependencies come in as
    // `--extern name=path.klib`, and the metadata goes to `--meta`.
    compilerId: str = "";
    metaPath: str = "";
    externNames: Vec<str>;
    externPaths: Vec<str>;

    // An index loop, not `for x in args`: a flag that takes a value has to consume the element
    // after it, and a loop variable gives no way to step past one. `args[0]` is the program's own
    // path, so the scan starts at 1.
    i: long = 1;
    while (i < args.len) {
        x: str = args[i];
        if (x == "--help" || x == "-h") {
            println(USAGE);
            return 0;
        } else if (x == "--output" || x == "-o") {
            if (i + 1 >= args.len) { fail("missing argument to --output"); }
            i = i + 1;
            output = args[i];
        } else if (x == "--emit" || x == "-e") {
            if (i + 1 >= args.len) { fail("missing argument to --emit"); }
            i = i + 1;
            emit = args[i];
        } else if (strStartsWith(x, "--emit=")) {
            emit = strSlice(x, 7, x.len - 7);
        } else if (x == "--trace-fold") {
            gTraceFold = true;
        } else if (x == "--time-phases") {
            gTimePhases = true;
        } else if (x == "--trace-opt") {
            gTraceOpt = true;
        } else if (x == "--no-thread") {
            gThreadOff = true;
        } else if (x == "--no-cse") {
            gCseOff = true;
        } else if (x == "--no-flow") {
            gFlowOff = true;
        } else if (x == "--klib-verify") {
            klibVerify = true;
        } else if (x == "--verify-regops") {
            verifyOps = true;
        } else if (x == "--lib") {
            gEmitLibrary = true;
            gInlineLibrary = true;
        } else if (x == "--klib") {
            gKlibMode = true;
        } else if (x == "--compiler-id" || x == "--meta" || x == "--extern") {
            if (i + 1 >= args.len) { failStr(format("missing argument to {}", x)); }
            i = i + 1;
            if (x == "--compiler-id") { compilerId = args[i]; }
            else if (x == "--meta") { metaPath = args[i]; }
            else {
                eq: long = strFind(args[i], "=").unwrapOr(-1);
                if (eq <= 0) { failStr(format("--extern wants name=path, not '{}'", args[i])); }
                externNames.push(strSlice(args[i], 0, eq));
                externPaths.push(strSlice(args[i], eq + 1, args[i].len - eq - 1));
            }
        } else if (x == "--use") {
            // The symbols another object already defines. Everything named here is referenced
            // rather than emitted, so the program has one copy of each.
            if (i + 1 >= args.len) { fail("missing argument to --use"); }
            i = i + 1;
            readSymbols(args[i]);
        } else if (strStartsWith(x, "--use=")) {
            readSymbols(strSlice(x, 6, x.len - 6));
        } else if (strStartsWith(x, "--fold-steps=")) {
            gStepLimit = flagNumber(x, 13);
        } else if (strStartsWith(x, "--fold-heap=")) {
            gHeapLimit = flagNumber(x, 12) * 1048576;
        } else if (x.len > 0 && charAt(x, 0) == '-') {
            failStr(format("unknown option '{}'", x));
        } else {
            input = x;
            inputs.push(x);
        }
        i = i + 1;
    }

    if (input.len == 0) { fail(USAGE); }
    if (output.len == 0) { output = "output.s"; }
    if (inputs.len() > 1 && !gKlibMode) { fail("several input files are a package build: add --klib"); }

    phaseStart();
    // The dependencies first: their modules, exports and facts are what the scan and every phase
    // after it consult in place of their source on disk.
    for k in 0..externNames.len() { loadKlib(externNames.get(k), externPaths.get(k)); }
    if (gKlibMode) {
        checkKlibConsistency();
        rankKlibs();
        if (metaPath.len == 0) { metaPath = keepString(format("{}.meta", output)); }
    }
    sc: Scanner;
    sc.scanAll(inputs);
    klibDeps: Vec<str>;
    if (gKlibMode) { klibDeps = settlePackage(&sc, inputs); }
    phaseEnd("scan + preprocess");

    if (emit == "pre") {
        for m in sc.modules {
            src: str = m.source;
            unsafe { writeBytes(src.ptr, src.len); }
        }
        flush();
        return 0;
    }

    if (emit == "tokens") {
        lx: Lexer = lexerOf(wholeProgram(&sc));
        toks: Vec<Token> = lx.all();
        line: String;
        for t in toks {
            line.clear();
            pushTokenLine(&line, t);
            println("{}", line);
        }
        flush();
        return 0;
    }

    if (emit == "ast" || emit == "typed") {
        p: Parser = parserOf("");
        page: long = parseProgram(&p, &sc);
        afterParse(&p.ast);
        // `typed` runs the middle end's typing pass first, so the dump shows what every
        // expression actually yields rather than only what syntax could decide.
        if (emit == "typed") { page = middleEnd(&p.ast, page); }
        text: String;
        dumpBlock(p.ast, &text, page, 0);
        unsafe { v: str = text.view(); writeBytes(v.ptr, v.len); }
        flush();
        return 0;
    }

    if (emit == "ir") {
        p: Parser = parserOf("");
        page: long = parseProgram(&p, &sc);
        afterParse(&p.ast);
        page = middleEnd(&p.ast, page);
        lw: Lowerer;
        lw.lowerProgram(&p.ast, page);
        // The dump shows what the back end will actually emit, which is the optimized IR.
        op: Opt;
        op.run(&lw.ir);
        rl: Relayout;
        rl.run(&lw.ir);
        op2: Opt;
        op2.afterInline = true;
        op2.run(&lw.ir);
        fl: Flow;
        fl.run(&lw.ir);
        text: String;
        dumpIR(lw.ir, &text);
        unsafe { v: str = text.view(); writeBytes(v.ptr, v.len); }
        flush();
        return 0;
    }

    // The LLVM path stops after lowering: `Opt` and `Relayout` do work LLVM does better, and
    // skipping them keeps `Jcc` and promoted temps out of a translation that would only have to
    // undo them.
    if (emit == "llvm") {
        p: Parser = parserOf("");
        page: long = parseProgram(&p, &sc);
        afterParse(&p.ast);
        page = middleEnd(&p.ast, page);
        lw: Lowerer;
        lw.lowerProgram(&p.ast, page);
        text: String;
        emitLlvm(&lw.ir, &text);
        unsafe { v: str = text.view(); writeBytes(v.ptr, v.len); }
        flush();
        return 0;
    }

    if (emit.len > 0) { fail("unknown --emit stage (pre|tokens|ast|typed|ir|llvm)"); }

    // `--verify-regops`: the registry the parse wrote, against its operation log replayed into an
    // empty one (`parse::regops`).
    if (verifyOps) {
        gOpLogOn = true;
        vp: Parser = parserOf("");
        parseProgram(&vp, &sc);
        if (verifyRegops(&vp.ast, vp.fnReturns) > 0) { return 1; }
        return 0;
    }

    // The whole pipeline: parse, type, lower, allocate, emit. A package build logs what its parse
    // writes to the registry, per module: that log is what a dependent replays.
    if (gKlibMode) { gOpLogOn = true; }
    gPhase = "parsing";
    ps: Parser = parserOf("");
    page: long = parseProgram(&ps, &sc);
    phaseEnd("lex + parse");
    if (gTimePhases) {
        eprintln("    ({} modules parsed, {} read from a .klib in {} ms)", sc.count() - gModulesLoaded, gModulesLoaded, gLoadUs / 1000);
    }
    // A package build writes its modules' trees now, before the checker rewrites a body.
    if (gKlibMode) {
        snapshotModules(&ps, &sc);
        // `--klib-verify`: every module written, read back and compared, and the registry
        // replayed (`KlibTree.verifyKlibTrees`, `parse::regops`).
        if (klibVerify) {
            bad: long = verifyKlibTrees(&ps);
            if (verifyPackageRegops(&ps) > 0) { bad = bad + 1; }
            if (bad > 0) { return 1; }
            return 0;
        }
        phaseEnd("write the module trees");
    }
    // Which functions came from a dependency, and the return types their compile settled.
    afterParse(&ps.ast);
    // Stamp every generic instance the program asked for, so the checker and everything after
    // it deal only in concrete types.
    page = middleEnd(&ps.ast, page);
    phaseStart();
    gPhase = "lowering";
    lw: Lowerer;
    lw.lowerProgram(&ps.ast, page);
    phaseEnd("lower");
    if (gTimePhases) {
        eprintln("    ({} functions lowered; {} of {} dependency bodies read)", lw.ir.funcs.len(), gBodiesRead, gLazyBodies.len());
    }
    gPhase = "optimizing";
    op: Opt;
    op.run(&lw.ir);
    // A package build keeps the IR of what it exports and its dependents could inline, and reads
    // in its dependencies' for the calls it makes into them (`irpack`).
    if (gKlibMode) {
        snapshotInlinable(&lw.ir);
        importInlinable(&lw.ir);
    }
    phaseEnd("optimize");
    if (gTimePhases && gKlibMode) { eprintln("    ({} bodies read for inlining across packages)", gShipImported); }
    // Every function's instructions and temps back into contiguous runs, so a pass that made one
    // longer has left the program in the shape the rest of the back end reads. On its own this is
    // the identity.
    rl: Relayout;
    rl.run(&lw.ir);
    phaseEnd("inline + relayout");
    // Again, over the spliced code. A body copied into its caller arrives with the copies that
    // bound its parameters and with whatever its own shape cost it in isolation; none of that had
    // been through the optimizer in this context. The first run is what makes bodies small enough
    // to be worth copying, and the second is what makes the copies worth having.
    op2: Opt;
    op2.afterInline = true;
    op2.run(&lw.ir);
    phaseEnd("optimize again");
    // Then across blocks, over the inlined code: constants, redundant loads, and the branches and
    // bounds checks what is already known decides (flow.k).
    fl: Flow;
    fl.run(&lw.ir);
    phaseEnd("flow");
    // A program built from packages starts by running theirs, each after what it depends on.
    if (gKlibMode) { gStartInits = startInits(); }
    gPhase = "emitting";
    em: Emitter;
    em.emitProgram(lw.ir);
    gPos = 0;
    gCtxFn = NO_SYM;
    gCtxInst = NO_SYM;
    gPhase = "writing the output";
    phaseEnd("emit");
    text: str = "";
    unsafe { text = em.outView(); }
    r: Result<long, long> = writeFileStr(output, text);
    match r {
        Ok(_)  { }
        Err(e) { eprintln("could not write {} (errno {})", output, e); return 1; }
    }
    // A library says what it exported, so a consumer does not have to re-derive it from source
    // both sides parse -- and cannot drift from it.
    if (gEmitLibrary) { writeSymbols(keepString(format("{}.syms", output))); }
    if (gKlibMode) {
        // What every key this compiler builds starts from; the build driver hands it down so it
        // is hashed once per build rather than once per package.
        if (compilerId.len == 0) { compilerId = compilerIdentity(); }
        writeKlibMeta(metaPath, &sc, compilerId, sc.packages.rootOf(inputs.get(0)), klibDeps, definesMain(&ps.ast));
    }
    return 0;
}

// One symbol per line, as a `--lib` build wrote it. Blank lines are skipped so the file can be
// concatenated from several without care.
local readSymbols path:str -> void {
    text: str = readSource(path);
    lines: Vec<str> = splitLines(text);
    for line in lines {
        one: str = strTrim(line);
        if (one.len == 0) { continue; }
        gUseSyms.put(keep(one), true);
    }
}

// What this object exported, written beside the assembly so a consumer can `--use` it.
local writeSymbols path:str -> void {
    text: String;
    for s in gExportedSyms {
        text.pushStr(s);
        text.push('\n');
    }
    v: str = "";
    v = keepString(text);
    r: Result<long, long> = writeFileStr(path, v);
    match r {
        Ok(_)  { }
        Err(e) { eprintln("could not write {} (errno {})", path, e); }
    }
}

// Every module, in the scanner's order, onto one page: one a dependency's `.klib` carries read
// from there, already parsed (`KlibTree.loadModuleSection`), and every other parsed from its own
// text, so nothing a module says depends on the text around it.
local parseProgram inout p:Parser inout sc:Scanner -> long {
    for m in sc.modules {
        kk: long = klibModule(m.path);
        if (kk >= 0) {
            t0: Instant = monotonic();
            loadModuleSection(p, kk, m.index);
            gLoadUs = gLoadUs + elapsedUs(t0);
        }
        else {
            p.beginModule(m.source, m.index);
            p.parseModule();
        }
    }
    return p.finishPage();
}

// Every module's rewritten source, in scan order, as one text, with the `#file` markers that keep
// each declaration attributed to its own file: what `--emit=tokens` shows.
local wholeProgram inout sc:Scanner -> str {
    all: String;
    for m in sc.modules { all.pushStr(m.source); }
    out: str = "";
    out = keepString(all);
    return out;
}

// What a package build is building: the package its modules declare, which every module scanned
// must either be in or have arrived in a `.klib` from. A module of some other package would be
// compiled into this object as well as into its own -- two copies of its storage -- so it is
// refused. Answers the package's direct dependencies, the standard library included, which is
// what its metadata records the keys of.
local settlePackage inout sc:Scanner inputs:Vec<str> -> Vec<str> {
    pkg: str = sc.packages.packageOf(inputs.get(0));
    gThisPkg = intern(pkg);
    for m in sc.modules {
        if (m.package == pkg) { continue; }
        // A dependency's module has to be one its own build compiled: anything else would be
        // compiled here as well as there.
        if (gUpstreamPkgs.has(m.package)) {
            if (klibModule(m.path) >= 0) { continue; }
            failStr(format("{} is a module of package '{}' that its .klib does not hold -- that package's build compiles the .k files of its root directory and what they include",
                           m.path, m.package));
        }
        failStr(format("{} belongs to package '{}', which is neither the one being built ('{}') nor one an --extern provides",
                       m.path, m.package, pkg));
    }
    deps: Vec<str>;
    idx: long = sc.packages.infoFor(inputs.get(0));
    for k in 0..sc.packages.depCountAt(idx) { deps.push(sc.packages.depAt(idx, k).name); }
    if (!(pkg == STDLIB_PKG) && gUpstreamPkgs.has(STDLIB_PKG)) { deps.push(STDLIB_PKG); }
    return deps;
}

// The startup initializers of the packages this one is built on, in dependency order.
local startInits -> Vec<str> {
    out: Vec<str>;
    order: Vec<long> = klibOrder();
    for at in order {
        init: str = gKlibs.get(at).init;
        if (init.len > 0) { out.push(init); }
    }
    return out;
}

// Whether this package defines the program's entry point.
local definesMain inout a:Ast -> bool {
    for f in a.fns {
        if (nameOf(f.name) == "main" && f.pkg == gThisPkg && f.body >= 0) { return true; }
    }
    return false;
}

// In a package build, which functions came from a dependency and what each was called when
// parsed (the key its facts are filed under), and the return types its compile settled.
local afterParse inout a:Ast -> void {
    if (!gKlibMode) { return; }
    noteParsedFunctions(a);
    applyExternReturns(a);
}
