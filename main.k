// The Kiln compiler's command line.
//
//   kilnc foo.k -o foo.s          compile a program to assembly
//   kilnc foo.k --emit=<stage>    print one intermediate representation and stop
//   kilnc build [root]            build a package and what it depends on (`1-cumulation/Build.k`)
#include <stdlib::{chars, file, io, result, string, time, vec}>
#include <support::compiler>
#include <parse::{diag, upstream, regops, treecodec, astdump, ast, parser}>
#include <cumul::{Module, Scanner, Klib, KlibOut, KlibTree, Build}>
#include <transform::{facts, check, eval, guard, mono}>
#include <pre::Preprocessor>
#include <codegen::{asm, lower, opt, flow, relayout, irdump, llvm, ir, irpack, effects, relax, scale, regalloc}>
#include <lex::{lexer, token}>

local USAGE: str = "usage: kilnc <file.k> [-o out.s] [options]\n       kilnc build [root] [-o exe] [--cache dir]\n       kilnc --klib <file.k>... [--extern name=path.klib]... [--meta file] [--compiler-id hex] -o out.s\n\noptions:\n  -o, --output <file>    write the assembly to <file> (default output.s)\n  --emit=<stage>         print one stage and stop: pre, tokens, ast, typed, ir or llvm\n  --lib                  compile a library: export every `pub` function, write no `_start`\n  --use <file>           take the symbols listed in <file> from another object\n  --time-phases          print how long each phase took\n  --trace-fold           print what the compile-time evaluator folded or could not\n  --trace-opt            print what the optimizer did\n  --trace-ipra           print what a call to each function may change\n  --no-flow, --no-relax, --no-thread, --no-cse, --no-hoist, --no-results, --no-build,\n  --no-scale, --no-rotate, --no-select, --no-loop-inline,\n  --no-short-memcpy, --no-exact-calls, --no-second-chance, --no-homes,\n  --no-wide-addr, --no-hoist-dup, --no-empty-loops, --no-forward-inline,\n  --no-splice-slots, --no-commute, --no-xor-bounds, --no-wide-const, --no-set-in-place,\n  --no-fill-loops, --no-sink-homes, --no-neg, --no-asm-out,\n  --no-scale-convert, --no-result-each,\n  --no-unroll, --no-refold, --no-free-seeds, --no-accumulate, --no-ipra\n                         turn one optimization off\n  --no-restrict          trust no borrowed parameter to be the only way to its bytes\n  --no-lent              take a local lent to a call as exposed from then on\n  --no-rodata            read nothing out of an immutable global's image\n  --no-moved-args        copy every struct taken by value in its callee, moved into the call or not\n  --ipra-asm-full        take a function holding an `asm` block to change every caller-saved register\n  --fold-steps=<n>       limit the compile-time evaluator to <n> steps\n  --fold-heap=<MiB>      limit its heap to <MiB> mebibytes\n  --verify-regops        check the registry against its operation log, then stop\n  --klib-verify          in a package build, check every module's tree reads back, then stop\n  -h, --help             print this and exit";

// The number after `--flag=`, which must be one, and positive.
local flagNumber flag:str at:long -> long {
    got: Option<long> = parseLong(strSlice(flag, at, flag.len - at));
    match got { Some(n) { if (n > 0) { return n; } } None { } }
    failStr(format("invalid value in `{}`: expected a positive number", flag));
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
    // A function held back for a macro that cannot run yet is another reason for a round: the
    // round checks (and stamps) the macro's callees, and the held function is retried. A round
    // that stamps nothing and frees nothing is stuck, and says on what. Two more reasons are an
    // implementation a derive stubbed that its macro has yet to write (see the derives in
    // check.k), and a method stamped for one, which waits for its types to be laid out.
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
            failStr(format("cannot prepare a macro: {}", ck.deferReason));
        }
        if (!stamping && heldBefore == 0 && ck.derivesRun == derivedBefore && ck.fnDone.len() == checkedBefore
            && ck.deriveQ.len() > 0 && ck.wanted.len() == 0 && ck.deferredCount() == 0) {
            failStr(format("cannot prepare a derive: {}", ck.deferReason));
        }
        rounds = rounds + 1;
    }
    if (ck.deriveWork() > 0) { failStr(format("derives did not settle after {} rounds: {}", MAX_STAMP_ROUNDS, ck.deferReason)); }
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
    cg.openObject = gOpenObject;     // what another object may call, or be called by, is out of sight
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
            if (i + 1 >= args.len) { failStr(format("missing argument to `{}`", x)); }
            i = i + 1;
            output = args[i];
        } else if (x == "--emit" || x == "-e") {
            if (i + 1 >= args.len) { failStr(format("missing argument to `{}`", x)); }
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
        } else if (x == "--no-restrict") {
            gRestrictOff = true;
        } else if (x == "--no-lent") {
            gLentOff = true;
        } else if (x == "--no-rodata") {
            gRodataOff = true;
        } else if (x == "--no-moved-args") {
            gMovedArgsOff = true;
        } else if (x == "--no-hoist") {
            gHoistOff = true;
        } else if (x == "--no-scale") {
            gScaleOff = true;
        } else if (x == "--no-rotate") {
            gRotateOff = true;
        } else if (x == "--no-select") {
            gSelectOff = true;
        } else if (x == "--no-loop-inline") {
            gLoopInlineOff = true;
        } else if (x == "--no-short-memcpy") {
            gShortCopyOff = true;
        } else if (x == "--no-exact-calls") {
            gExactCallsOff = true;
        } else if (x == "--no-second-chance") {
            gSecondChanceOff = true;
        } else if (x == "--no-homes") {
            gHomesOff = true;
        } else if (x == "--no-sink-homes") {
            gSinkHomesOff = true;
        } else if (x == "--no-commute") {
            gCommuteOff = true;
        } else if (x == "--no-xor-bounds") {
            gXorBoundsOff = true;
        } else if (x == "--no-wide-const") {
            gWideConstOff = true;
        } else if (x == "--no-neg") {
            gNegOff = true;
        } else if (x == "--no-set-in-place") {
            gSetInPlaceOff = true;
        } else if (x == "--no-fill-loops") {
            gFillLoopsOff = true;
        } else if (x == "--no-result-each") {
            gResultEachOff = true;
        } else if (x == "--no-scale-convert") {
            gScaleConvertOff = true;
        } else if (x == "--no-unroll") {
            gUnrollOff = true;
        } else if (x == "--no-refold") {
            gRefoldOff = true;
        } else if (x == "--no-accumulate") {
            gAccumulateOff = true;
        } else if (x == "--no-ipra") {
            gIpraOff = true;
        } else if (x == "--ipra-asm-full") {
            gIpraAsmFull = true;
        } else if (x == "--trace-ipra") {
            gTraceIpra = true;
        } else if (x == "--no-free-seeds") {
            gFreeSeedsOff = true;
        } else if (x == "--no-asm-out") {
            gAsmOutOff = true;
        } else if (x == "--no-wide-addr") {
            gWideAddrOff = true;
        } else if (x == "--no-hoist-dup") {
            gHoistDupOff = true;
        } else if (x == "--no-empty-loops") {
            gEmptyLoopsOff = true;
        } else if (x == "--no-forward-inline") {
            gForwardInlineOff = true;
        } else if (x == "--no-splice-slots") {
            gSpliceSlotsOff = true;
        } else if (x == "--no-results") {
            gResultsOff = true;
        } else if (x == "--no-build") {
            gBuildOff = true;
        } else if (x == "--no-cse") {
            gCseOff = true;
        } else if (x == "--no-flow") {
            gFlowOff = true;
        } else if (x == "--no-relax") {
            gRelaxOff = true;
        } else if (x == "--klib-verify") {
            klibVerify = true;
        } else if (x == "--verify-regops") {
            verifyOps = true;
        } else if (x == "--lib") {
            gEmitLibrary = true;
            gInlineLibrary = true;
            gOpenObject = true;
        } else if (x == "--klib") {
            gKlibMode = true;
        } else if (x == "--compiler-id" || x == "--meta" || x == "--extern") {
            if (i + 1 >= args.len) { failStr(format("missing argument to `{}`", x)); }
            i = i + 1;
            if (x == "--compiler-id") { compilerId = args[i]; }
            else if (x == "--meta") { metaPath = args[i]; }
            else {
                eq: long = strFind(args[i], "=").unwrapOr(-1);
                if (eq <= 0) { failStr(format("invalid `--extern` argument `{}`\nhelp: write `--extern name=path.klib`", args[i])); }
                externNames.push(strSlice(args[i], 0, eq));
                externPaths.push(strSlice(args[i], eq + 1, args[i].len - eq - 1));
            }
        } else if (x == "--use") {
            // The symbols another object already defines. Everything named here is referenced
            // rather than emitted, so the program has one copy of each.
            if (i + 1 >= args.len) { failStr(format("missing argument to `{}`", x)); }
            i = i + 1;
            readSymbols(args[i]);
            gOpenObject = true;
        } else if (strStartsWith(x, "--use=")) {
            readSymbols(strSlice(x, 6, x.len - 6));
            gOpenObject = true;
        } else if (strStartsWith(x, "--fold-steps=")) {
            gStepLimit = flagNumber(x, 13);
        } else if (strStartsWith(x, "--fold-heap=")) {
            gHeapLimit = flagNumber(x, 12) * 1048576;
        } else if (x.len > 0 && charAt(x, 0) == '-') {
            failStr(format("unknown option `{}`\nhelp: `kilnc --help` lists the options", x));
        } else {
            input = x;
            inputs.push(x);
        }
        i = i + 1;
    }

    if (input.len == 0) { fail("no input file\nhelp: `kilnc <file.k> -o out.s` compiles a program; `kilnc --help` lists the options"); }
    if (output.len == 0) { output = "output.s"; }
    if (inputs.len() > 1 && !gKlibMode) { fail("more than one input file\nhelp: several files are compiled together as one package with `--klib`"); }

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
        sa: Scaler;
        sa.run(&lw.ir);
        if (!gFillLoopsOff) { op2.fillLoopsAll(&lw.ir); }
        if (!gUnrollOff) { op2.unrollAll(&lw.ir); }
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

    if (emit.len > 0) { failStr(format("unknown `--emit` stage `{}`\nnote: the stages are pre, tokens, ast, typed, ir and llvm", emit)); }

    // `--verify-regops`: the registry the parse wrote, against its operation log replayed into an
    // empty one (`parse::regops`). Also after a parse with errors, which is what shows that each
    // declaration taken back took its operations and its entries with it.
    if (verifyOps) {
        gOpLogOn = true;
        vp: Parser = parserOf("");
        parseModules(&vp, &sc);
        if (verifyRegops(&vp.ast, vp.fnReturns) > 0) { return 1; }
        stopIfErrors();
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
    // A package build keeps what each function it exports may write, for its dependents.
    if (gKlibMode) { fxNoteExports(&lw.ir); }
    // Then element addresses into one addressing mode each, which only the emitter reads.
    sa: Scaler;
    sa.run(&lw.ir);
    if (gTraceOpt) { eprintln("scale: {} accesses indexed", gScaled); }
    // A loop that only clears a range of a frame slot's array: one block zero.
    if (!gFillLoopsOff) { op2.fillLoopsAll(&lw.ir); }
    if (!gUnrollOff) { op2.unrollAll(&lw.ir); }
    phaseEnd("flow");
    // A program built from packages starts by running theirs, each after what it depends on.
    if (gKlibMode) { gStartInits = startInits(); }
    gPhase = "emitting";
    em: Emitter;
    em.emitProgram(lw.ir);
    if (gTraceOpt) {
        eprintln("relax: {} jumps short, {} near, {} functions left as written", em.relax.nShort, em.relax.nNear, em.relax.nKept);
    }
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
        Err(e) { eprintln("error: cannot write `{}` (errno {})", output, e); return 1; }
    }
    // A library says what it exported, so a consumer does not have to work it out again from the
    // source both sides parse, and the two cannot drift apart.
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
        Err(e) { eprintln("error: cannot write `{}` (errno {})", path, e); }
    }
}

// Every module, in the scanner's order, onto one page: one a dependency's `.klib` carries read
// from there, already parsed (`KlibTree.loadModuleSection`), and every other parsed from its own
// text, so nothing a module says depends on the text around it. The parser goes on past a
// declaration with an error in it to report the next; the compile stops here if there was one.
local parseProgram inout p:Parser inout sc:Scanner -> long {
    page: long = parseModules(p, sc);
    stopIfErrors();
    return page;
}
local parseModules inout p:Parser inout sc:Scanner -> long {
    for m in sc.modules {
        kk: long = klibModule(m.path);
        if (kk >= 0) {
            t0: Instant = monotonic();
            c: KlibCheck = loadModuleSection(p, kk, m.index);
            if (!c.ok) {
                info: KlibInfo = gKlibs.get(gKlibModules.get(kk).klib);
                cannotUse(info.name, info.path, c);
            }
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

// What a package build is building: the package its modules declare. Every module scanned must
// either belong to it or have arrived in a `.klib`. A module of some other package would be
// compiled into this object as well as into its own, giving two copies of its storage, so it is
// refused. Returns the package's direct dependencies, the standard library included, which are
// the ones its metadata records the keys of.
local settlePackage inout sc:Scanner inputs:Vec<str> -> Vec<str> {
    pkg: str = sc.packages.packageOf(inputs.get(0));
    gThisPkg = intern(pkg);
    for m in sc.modules {
        if (m.package == pkg) { continue; }
        // A dependency's module has to be one its own build compiled. Anything else would be
        // compiled here as well as there.
        if (gUpstreamPkgs.has(m.package)) {
            if (klibModule(m.path) >= 0) { continue; }
            failStr(format("`{}` belongs to package `{}`, but that package's `.klib` does not contain it\nnote: a package's build compiles the `.k` files in its root directory and what they include",
                           m.path, m.package));
        }
        failStr(format("`{}` belongs to package `{}`, which is not the package being built (`{}`) and was not given with `--extern`",
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
