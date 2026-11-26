// The native back end: the IR written out as x86-64 NASM assembly.
//
// Each function gets one frame. A spilled temp is loaded into a scratch register for each use,
// which is why `rax` and `rdx` are never allocated. The calling convention is the compiler's own:
// argument `i` goes in register `i` and the result comes back in `rax`. Every scalar temp holds
// a canonical 64-bit word, sign- or zero-extended according to its own type.
#include <{cfg, ir, regalloc, lower, relax}>
#include <parse::{ast, upstream, registry, types}>
#include <transform::{eval, facts}>
#include <stdlib::{chars, map, mem, option, fmt, string, vec}>
#include <support::compiler>

// `--lib`: emit an object meant to be linked into a program rather than a program. Every `pub`
// function is kept and exported, and no `_start` is written.
pub var gEmitLibrary: bool = false;

// `--no-rotate`: every loop keeps its jump back to the test at its top (`markRotations`).
pub var gRotateOff: bool = false;
// `--no-rotate-join`: a loop whose last block is a join some branch reaches conditionally keeps
// its jump back (`markRotations`).
pub var gRotateJoinOff: bool = false;

// `--no-select`: every branch is written as a branch, none as conditional moves (`markSelects`).
pub var gSelectOff: bool = false;

// `--no-short-memcpy`: a `memcpy` of a constant length is `rep movsb` like any other
// (`emitShortCopy`).
pub var gShortCopyOff: bool = false;
// `--no-set-in-place`: a comparison's truth value and a `~` are formed in rax and copied out
// (`emitCompare`, `BNot`).
pub var gSetInPlaceOff: bool = false;
// `--no-frame-operand`: a right operand in the frame is loaded into rdx before a comparison or
// `+ - * & | ^` reads it, rather than read where it lies (`rightInPlace`).
pub var gFrameOperandOff: bool = false;
// `--trace-ipra`: print what a call to each function may change (`finishMask`).
pub var gTraceIpra: bool = false;

// The longest `memcpy` of a constant length written as moves rather than `rep movsb`.
pub SHORT_COPY_BYTES: long = 128;

// The symbols another object already defines, read from the `.syms` file its `--lib` build wrote
// (`--use`). Anything named here is not emitted again: it is declared `extern`, and the linker
// finds the one copy.
//
// This is a list of what was actually emitted, not a rule worked out again from the source both
// sides parse. A rule would have to agree with the other build forever, and anywhere the two
// drifted apart would be a duplicate symbol at best and, at worst, two copies of one piece of
// storage (two heaps, two stdout buffers) with no error anywhere.
pub var gUseSyms: HashMap<str, bool> = map![];

// What this object exported, in the order it was written. `--lib` puts it beside the assembly.
pub var gExportedSyms: Vec<str> = vec![];

// A program linked from packages: the startup initializers of the packages it is built on, in
// the order `_start` must call them (each after everything it depends on).
pub var gStartInits: Vec<str> = vec![];

// What a package build's object holds beyond its exports: the generic instances, glue and derived
// methods it stamped (local to it), and its vtables. The `.klib` records them, so a later part
// can reuse them instead of stamping them again.
pub var gEmittedLocal: Vec<str> = vec![];
pub var gEmittedVtables: Vec<str> = vec![];

// The generic instance functions this package build compiled and exports (`instanceAlias`), in
// the order they were written: what its `.klib` lists for a dependent to link to.
pub var gExportedInst: Vec<Sym> = vec![];

// The global name a package exports one of its instance functions under: its local label and the
// package. Package-qualified, because two packages that cannot see each other may both compile the
// same instance, and both have to link into one program.
pub instanceAlias name:str -> str {
    s: String = format("{}$$", fnLabel(name));
    // A package of one file is named by its path, so a character a label cannot hold is written
    // as `$` followed by its code.
    pkg: str = nameOf(gThisPkg);
    for i in 0..pkg.len {
        c: long = charAt(pkg, i);
        if ((c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z') || (c >= '0' && c <= '9') || c == '_') { s.push(c as char); }
        else {
            s.push('$');
            s.pushLong(c);
        }
    }
    out: str = "";
    out = keepString(s);
    return out;
}

// The range of immediate values worth keeping the text of. Almost every immediate in real code
// is a small offset, a width or a count.
local NUM_CACHE_LO: long = 0 - 256;
local NUM_CACHE_HI: long = 4096;

pub SCRATCH: long = REG_RAX;
pub SCRATCH2: long = REG_RDX;

// A constant divisor's multiplier and shift (`divMagic`, `emitDivideConst`).
pub struct DivMagic { m: long, s: long, add: bool }

// A branch written as conditional moves (`markSelects`): `if (c) goto L; arm; L:` (a triangle),
// or `if (c) goto L1; armA; goto L2; L1: armB; L2:` (a diamond). Each field is an index into the
// function's run (-1: none).
pub struct SelRegion {
    br: long,               // the branch
    start: long,            // the first instruction written in its place: the branch, or the value it is fused with
    end: long,              // the last one; the label after it is written as usual
    a0: long, a1: long,     // the triangle's arm, or the diamond's first (run when the branch is not taken)
    b0: long, b1: long,     // the diamond's second arm (run when it is)
    early: long,            // an arm's one instruction computed into rax before the comparison
    late: long,             // the diamond's arm written in place after it: 0 for A, 1 for B
    direct: Temp,           // the other arm's one copy, moved from its own register (NO_TEMP: none)
    inc: bool               // the triangle's `d = d + 1` or `d - 1`, added as the flag
}

pub struct Emitter {
    out: String,
    ra: RegAlloc,
    slots: HashMap<long, long>,  // variable name (its number) -> byte offset from rbp
    frame: long,                 // bytes used so far
    spillAt: Vec<long>,          // spilled temp of this function -> its offset, or 0
    rematText: Vec<str>,         // ...or the operand that computes it again (`materialize`)
    rematVal: Vec<long>,         // ...and for a constant, its value
    // ...and for an address a load or store can name in its own addressing mode, the base that
    // mode starts from (`rbp`, or `rel <symbol>`; "" for any other) and, for a frame slot, how far
    // below `rbp` it lies (`address`)
    rematBase: Vec<str>,
    rematOff: Vec<long>,
    addrDisp: long,              // what `address` adds to the access's own offset
    // A division whose result only a branch reads (`emitFusedCompare`) leaves it in `divRes`, the
    // scratch register it was formed in, rather than storing it.
    keepDiv: bool,
    divRes: long,
    xmmSaveAt: Vec<long>,        // per callee-saved `xmm` register this function uses, its slot
    spillBase: Temp,             // ...indexed from here, this function's first temp
    // Every `file:line` a bounds check can report, deduplicated. Collected while the code is
    // emitted and written out with the rest of `.data` afterwards, which is the order
    // `emitProgram` already runs in.
    locs: Vec<Sym>,
    locIx: HashMap<long, long>,  // a location (its number) -> its index in `locs`
    // Declared-elsewhere functions this object actually calls. Only these get an `extern`
    // directive: declaring a symbol nothing references makes the linker demand a definition for
    // it, which is exactly the opposite of what a declaration is for.
    liveExtern: HashMap<str, bool>,
    externOrder: Vec<str>,          // the same, in the order first reached, for a stable dump
    // ...and the same for a global another object owns. A global is storage, so a second copy is
    // not a naming problem: it is a second heap, or a second stdout buffer, with nothing to say
    // so. These are referenced, never emitted.
    liveExternGlobal: HashMap<str, bool>,
    externGlobalOrder: Vec<str>,
    aggAt:   Vec<long>,          // aggregate scratch slot -> its offset, where `aggFn` is this function's
    aggFn:   Vec<long>,          // the function (`fnSeq`) that last placed each scratch slot
    // The handler labels of this function's `recover` statements, each to its record's slot: a
    // `raise` lands at the label, where the registers the record kept are put back.
    landing: HashMap<long, long>,
    fnSeq:   long,               // functions emitted so far, what `aggFn` is stamped with
    argAt:   Vec<long>,          // argument staging slot -> its offset
    // A call's general-register arguments still to be moved (`emitArgs`): each one's register,
    // the register its value is in (-1: memory, or computed in place), and its temp.
    pmDst: Vec<long>, pmSrc: Vec<long>, pmTemp: Vec<Temp>,
    seedDirect: Vec<bool>,       // per parameter seed: its temp is filled by the prologue, its slot unused
    // The frame slots this function takes the address of, and the globals any function does: a
    // store through that address writes a narrow value at its own width, so a read by name
    // extends it again.
    addrTaken: HashMap<long, bool>,
    globalsLent: HashMap<long, bool>,
    frameless: bool,             // this function keeps no frame: no `rbp`, nothing addressed through it
    frameSub: long,              // what the prologue takes off `rsp` below its pushes (`frameBytes`)
    // Loops whose jump back is written as their test (`markRotations`): per instruction, the test
    // a jump back is made into (-1: none), and the label a test gets after it (NO_SYM: none); per
    // jump back, its loop's header label and the label its own block starts at (-1: none); and
    // per jump into such a block, the jump back whose block and test are written in its place.
    rotFrom: Vec<long>,
    rotLabel: Vec<Sym>,
    rotHead: Vec<long>,
    latchAt: Vec<long>,
    dupTo: Vec<long>,
    // Branches written as conditional moves (`markSelects`): per instruction, the region that starts
    // there (an index into `sels`, -1: none), and whether it lies inside one, where no branch or
    // label of its own is written.
    selAt: Vec<long>,
    selIn: Vec<bool>,
    sels: Vec<SelRegion>,
    atLast: bool,                // the instruction being emitted is the body's last
    coldSeq: long,               // labels made for cold runs that had none
    calleeAt: long,              // where an indirect call parks its callee

    // The cold half of each bounds check, held back and written after the function's `ret` so the
    // hot stream carries only a compare and a not-taken branch.
    cold: String,
    boundsN: long,               // unique label counter for bounds checks
    heapRegions: long,           // how many 64 KiB static heap regions have been opened
    // Text built once and reused: frame offsets, global references, small immediates. Every one
    // of these is asked for several times per instruction.
    frameCache: Vec<str>,
    globalText: HashMap<long, str>,   // by the name, as its number
    relBaseText: HashMap<long, str>,  // `rel <symbol>` for a global, the same way
    relText: HashMap<str, str>,
    numCache: Vec<str>,
    addrText: String,            // `base + index*scale`, rebuilt for each indexed access
    lineAt: long,                // where the line being written starts
    relaxing: bool,              // inside a function's text: lines go to `relax`
    needBounds: bool,            // emit the abort routine only if a check can reach it
    needSlice: long,             // ...and each slice report a check can reach: bit k for kind k

    // What `main` reaches (`markReachable`): the functions emitted, the vtables, the globals,
    // the images (a global's bytes, a heap block's) and the string literals.
    live: HashMap<str, bool>,
    liveVt: HashMap<str, bool>,
    liveGlobal: HashMap<str, bool>,
    liveImage: Vec<bool>,
    liveStr: Vec<bool>,
    needHeapCentral: bool,         // a reached `asm` block names the allocator's shared state
    edgeFrom: Vec<long>, edgeTo: Vec<long>,   // the direct calls that return, by function index (`markReachable`)
    // Where in `cold` lies text that never returns (a bounds check's report, a cold run), as
    // pairs of offsets: what it writes is nothing the function's caller sees (`Relax.aside`).
    coldAside: Vec<long>,
    relax: Relax                   // which jumps of a function just written can be short
}

methods Emitter for Default {
    new -> Emitter {
        o: String; r: RegAlloc; cd: String; at: String;
        return Emitter { out: o, ra: r, slots: map![], frame: 0, spillAt: vec![], rematText: vec![], rematVal: vec![], rematBase: vec![], rematOff: vec![], addrDisp: 0, keepDiv: false, divRes: 0, xmmSaveAt: vec![], spillBase: 0, locs: vec![], locIx: map![], liveExtern: map![], externOrder: vec![], liveExternGlobal: map![], externGlobalOrder: vec![],
                         aggAt: vec![], aggFn: vec![], landing: map![], fnSeq: 0, argAt: vec![], pmDst: vec![], pmSrc: vec![], pmTemp: vec![], seedDirect: vec![], addrTaken: map![], globalsLent: map![], frameless: false, frameSub: 0, rotFrom: vec![], rotLabel: vec![], rotHead: vec![], latchAt: vec![], dupTo: vec![], selAt: vec![], selIn: vec![], sels: vec![], atLast: false, coldSeq: 0,
                         calleeAt: 0, cold: cd, boundsN: 0, heapRegions: 0, frameCache: vec![], globalText: map![], relBaseText: map![], relText: map![], numCache: vec![], addrText: at, lineAt: 0, relaxing: false, needBounds: false, needSlice: 0,
                         live: map![], liveVt: map![], liveGlobal: map![], liveImage: vec![], liveStr: vec![],
                         needHeapCentral: false, edgeFrom: vec![], edgeTo: vec![], coldAside: vec![], relax: Relax.new() };
    }
}

methods Emitter {
    put &self s:str -> void { self.out.pushStr(s); }
    // Every line of a function's text ends here, so `relax.k` is told each one as it is written
    // and never reads the text back.
    putLine &self s:str -> void {
        self.out.pushStr(s);
        if (self.relaxing) { self.relax.line(&self.out, self.lineAt, self.out.length()); }
        self.out.push('\n');
        self.lineAt = self.out.length();
    }
    // A line the emitter did not compose (an `asm` block's): it may hold a comment or a quote.
    putRawLine &self s:str -> void {
        self.out.pushStr(s);
        self.out.push('\n');
        if (self.relaxing) { self.relax.text(&self.out, self.lineAt, self.out.length()); }
        self.lineAt = self.out.length();
    }
    putNum &self v:long -> void { self.out.pushLong(v); }
    // `memOperand`, written straight into the output rather than built and interned.
    putMem &self base:str off:long w:long -> void {
        if (w == 1) { self.out.pushStr("byte "); }
        if (w == 2) { self.out.pushStr("word "); }
        if (w == 4) { self.out.pushStr("dword "); }
        if (w == 8) { self.out.pushStr("qword "); }
        self.out.push('[');
        self.out.pushStr(base);
        if (off > 0) { self.out.pushStr(" + "); self.out.pushLong(off); }
        if (off < 0) { self.out.pushStr(" - "); self.out.pushLong(0 - off); }
        self.out.push(']');
    }

    // ─── the program ─────────────────────────────────────────────────────────

    emitProgram &self p:IRProgram -> void {
        for i in 0..p.code.len() {
            if (p.code[i].op == IROp.AddrOf && p.code[i].isGlobal && p.code[i].name != NO_SYM) {
                self.globalsLent.put(p.code[i].name as long, true);
            }
        }
        self.markReachable(p);
        self.emitLinkage(p);
        self.putLine("section .text");
        // Each function is compiled after the functions it calls, so that a call to one already
        // written changes only what that one may change (`RegAlloc.siteMask`), and then the text
        // is put back in the program's order, so where a function lands does not depend on it.
        self.relax.wantRegs = !gIpraOff;
        if (!gIpraOff) { self.noteNoReturns(p); }
        order: Vec<long> = self.calleesFirst(p);
        textFrom: Vec<long>; textTo: Vec<long>;
        for f in 0..p.funcs.len() { textFrom.push(-1); textTo.push(-1); }
        regionAt: long = self.out.length();
        for k in 0..order.len() {
            f: long = order.get(k);
            textFrom.set(f, self.out.length());
            self.emitFunction(p, p.funcs.get(f));
            textTo.set(f, self.out.length());
        }
        if (!gIpraOff) { self.inProgramOrder(regionAt, textFrom, textTo); }
        for f in 0..p.funcs.len() {
            if (textFrom.get(f) < 0) { continue; }
            fn: IRFunc = p.funcs.get(f);
            if (gKlibMode && gInstanceFp.has(nameOf(fn.name))) { gExportedInst.push(fn.name); }
            if (gKlibMode && !fn.isPub) { gEmittedLocal.push(fnLabelOf(fn.name)); }
        }
        // A library defines no entry point: the program object it is linked into has one, and
        // two `_start`s do not link.
        if (self.entryHere(p)) { self.emitStart(p); }
        self.emitBoundsFail();
        self.emitData(p);
    }

    // The functions this object defines, by index, in the order they are compiled: with
    // `--no-ipra` the program's, otherwise each after the functions it calls (a depth-first walk
    // over direct calls that return, each finished after its callees). A call into a cycle the
    // walk is still inside reaches a function not yet written, which `siteMask` takes as changing
    // every register.
    calleesFirst &self p:IRProgram -> Vec<long> {
        order: Vec<long>;
        nf: long = p.funcs.len();
        here: Vec<bool>;
        for f in 0..nf {
            here.push(self.live.has(nameOf(p.funcs.get(f).name)) && !gUseSyms.has(fnLabelOf(p.funcs.get(f).name)));
        }
        if (gIpraOff) {
            for f in 0..nf { if (here.get(f)) { order.push(f); } }
            return order;
        }
        // Each function's callees, from the calls `markReachable` kept, as runs of `to`.
        first: Vec<long>; to: Vec<long>; fill: Vec<long>;
        for f in 0..nf + 1 { first.push(0); }
        for e in 0..self.edgeFrom.len() { first.set(self.edgeFrom.get(e) + 1, first.get(self.edgeFrom.get(e) + 1) + 1); }
        for f in 0..nf { first.set(f + 1, first.get(f + 1) + first.get(f)); fill.push(first.get(f)); }
        for e in 0..self.edgeTo.len() { to.push(0); }
        for e in 0..self.edgeFrom.len() {
            a: long = self.edgeFrom.get(e);
            to.set(fill.get(a), self.edgeTo.get(e));
            fill.set(a, fill.get(a) + 1);
        }
        state: Vec<long>;               // 0 not reached, 1 on the walk, 2 finished
        for f in 0..nf { state.push(0); }
        stF: Vec<long>; stAt: Vec<long>;   // the walk: a function, and its next callee to look at
        for root in 0..nf {
            if (!here.get(root) || state.get(root) != 0) { continue; }
            stF.push(root); stAt.push(first.get(root)); state.set(root, 1);
            while (stF.len() > 0) {
                top: long = stF.len() - 1;
                f: long = stF.get(top);
                i: long = stAt.get(top);
                next: long = -1;
                while (i < first.get(f + 1) && next < 0) {
                    g: long = to.get(i);
                    i = i + 1;
                    if (here.get(g) && state.get(g) == 0) { next = g; }
                }
                stAt.set(top, i);
                if (next >= 0) {
                    state.set(next, 1);
                    stF.push(next); stAt.push(first.get(next));
                } else {
                    stF.pop(); stAt.pop();
                    state.set(f, 2);
                    order.push(f);
                }
            }
        }
        return order;
    }

    // The text of the functions, written in the order `calleesFirst` gave from `from` on, put back
    // in the program's order: function `f`'s text was [textFrom[f], textTo[f]).
    inProgramOrder &self from:long textFrom:Vec<long> textTo:Vec<long> -> void {
        fresh: String;
        fresh.reserve(self.out.length());
        text: str = "";
        unsafe { text = self.out.view(); }
        fresh.pushStr(strSlice(text, 0, from));
        for f in 0..textFrom.len() {
            if (textFrom.get(f) < 0) { continue; }
            fresh.pushStr(strSlice(text, textFrom.get(f), textTo.get(f) - textFrom.get(f)));
        }
        self.out = take(&fresh);
        self.lineAt = self.out.length();
    }

    // A call that never returns changes nothing anything after it could see: a call to a function
    // the checker found never returns (`gNoReturnFns`, what the lowerer marks a call `noReturn`
    // by), and one to the stubs `emitFailReport` writes, which end the process. A raise that one
    // of them makes lands in a `recover` handler, and a function holding one may change
    // anything (`finishMask`).
    noteNoReturns &self p:IRProgram -> void {
        for f in 0..p.funcs.len() {
            if (gNoReturnFns.has(nameOf(p.funcs.get(f).name))) { self.noReturnLabel(fnLabelOf(p.funcs.get(f).name)); }
        }
        self.noReturnLabel("__methBoundsFail");
        self.noReturnLabel("__methRangeFail");
        self.noReturnLabel("__methOrderFail");
        self.noReturnLabel("__methStartFail");
    }
    noReturnLabel &self label:str -> void {
        self.relax.calls.put(label, 0);
        if (gTraceIpra) { eprintln("ipra-noreturn {}", label); }
    }

    // What a call to `fn` may change, now that its text is whole (`Relax.regs`): what its lines
    // name and write and what the functions it calls may change, with the scratch added and the
    // callee-saved registers taken out, since its prologue and epilogue put back every one it
    // uses. A function holding a `recover` handler may change anything: a raise from below lands
    // in it with whatever the code in between left, and it then returns normally. With
    // `--ipra-asm-full` so may one holding an `asm` block.
    finishMask &self p:IRProgram fn:IRFunc -> void {
        m: long = self.relax.regs | MASK_SCRATCH;
        if (fn.holdsRecover) { m = MASK_FULL; }
        if (gIpraAsmFull) {
            for i in 0..fn.instrCount { if (p.code[fn.firstInstr + i].op == IROp.Asm) { m = MASK_FULL; } }
        }
        m = m & MASK_FULL;
        self.ra.fnMask.put(fn.name as long, m);
        if (!gNoReturnFns.has(nameOf(fn.name))) { self.relax.calls.put(fnLabelOf(fn.name), m); }
        if (gTraceIpra) { self.traceMask(fn, m); }
    }

    // `--trace-ipra`: each function's set, one line each on stderr, for `scripts/ipracheck.sh`.
    traceMask &self fn:IRFunc m:long -> void {
        s: String;
        for r in 0..REG_SLOTS + 1 {
            if ((m & (1 << r)) == 0) { continue; }
            s.push(' ');
            if (r == REG_SLOTS) { s.pushStr("xmm*"); } else { s.pushStr(regName64(r)); }
        }
        unsafe { eprintln("ipra {}{}", fnLabelOf(fn.name), s.view()); }
    }

    // Whether this object is the program's entry: it defines `_start` (and `__kiln_fini`).
    entryHere &self p:IRProgram -> bool {
        return !gEmitLibrary && (!gKlibMode || self.mainLabelOrEmpty(p).len > 0);
    }

    // What crosses the edge of this object, in both directions.
    //
    // `pub` is the export: a definition another object may call, so it gets a `global`. `pkg` and
    // `local` get nothing. They are internal to this object either way, and differ only in what
    // the checker allows. The import is a `pub` declaration with no body, and only the ones
    // something here actually calls: declaring a symbol nothing references would make the linker
    // demand a definition for it.
    //
    // Emitted before `.text` so NASM has seen every name before it meets a reference to one.
    emitLinkage &self p:IRProgram -> void {
        for f in 0..p.funcs.len() {
            fn: IRFunc = p.funcs.get(f);
            // Only a library exports. A program's object is linked with others that each
            // compiled the same standard library in, so exporting `pub mem::memcpy` from both
            // would be a duplicate definition, which the linker refuses.
            if (!(gEmitLibrary || gKlibMode) || !fn.isPub || !self.live.has(nameOf(fn.name))) { continue; }
            if (gUseSyms.has(fnLabelOf(fn.name))) { continue; }   // another object's already
            self.put("global ");
            self.putLine(fnLabelOf(fn.name));
            gExportedSyms.push(fnLabelOf(fn.name));
        }
        // A library exports its storage too, and all of it: a global is not a name a consumer
        // must be allowed to write, it is the one copy that has to be shared. Visibility governs
        // who may name it in source; linkage has to make sure there is only one.
        for g in 0..p.globals.len() {
            n: str = nameOf(p.globals.get(g));
            if (!(gEmitLibrary || gKlibMode) || !self.liveGlobal.has(n)) { continue; }
            if (gUseSyms.has(globalSymbol(n))) { continue; }
            self.put("global ");
            self.putLine(globalSymbol(n));
            gExportedSyms.push(globalSymbol(n));
        }
        for i in 0..p.externs.len() {
            n: Sym = p.externs.get(i);
            if (!self.liveExtern.has(nameOf(n))) { continue; }
            self.put("extern ");
            self.putLine(fnLabelOf(n));
        }
        // Everything another object already defines and this one reached.
        self.emitUsedExterns();
        // The `exit` builtin runs the program's `@fini` hooks through the entry object's
        // `__kiln_fini`; an object that is not the entry calls it from outside.
        if (gUsesFini && !self.entryHere(p)) { self.putLine("extern __kiln_fini"); }
    }

    // The `extern` directives for symbols a `--use` list said belong to another object. Written
    // from the live sets, so a list naming a thousand symbols costs a directive only for the ones
    // actually reached.
    emitUsedExterns &self -> void {
        for i in 0..self.externOrder.len() {
            k: str = self.externOrder.get(i);
            if (!gUseSyms.has(fnLabel(k))) { continue; }
            self.put("extern ");
            self.putLine(fnLabel(k));
        }
        for i in 0..self.externGlobalOrder.len() {
            self.put("extern ");
            self.putLine(self.externGlobalOrder.get(i));
        }
    }

    // Reached, and defined elsewhere. Recorded once, in the order first met.
    noteExtern &self n:str -> void {
        if (self.liveExtern.has(n)) { return; }
        self.liveExtern.put(n, true);
        self.externOrder.push(n);
    }

    // ─── what the program reaches ────────────────────────────────────────────

    // Only what `main` can reach is emitted. A function is reached by a call, by taking its
    // address, through a vtable a trait object is built from, by its name spelled inside an `asm`
    // block, or through a pointer the evaluator laid into `.data`. A global is reached by a load, a
    // store or its address in a reached function, by its label spelled in `asm`, or through a
    // pointer in a reached image. An image (a global's bytes, or a heap block's) is reached through
    // its global or through a pointer in another reached image, and a string literal through a
    // reached instruction or image. A vtable is reached in the same ways as a function.
    //
    // A program includes far more than it uses. Twenty lines that go through `io` and `vec` lower
    // to 425 functions and run a few dozen of them. Without this, every other one would be
    // register-allocated, written out and assembled, at a cost that grows faster than the text,
    // and every program would carry `ast`'s operator table (a folded Vec nobody reads) in a
    // 64 KiB-aligned static region.
    markReachable &self p:IRProgram -> void {
        byName: HashMap<str, long>;
        byLabel: HashMap<str, long>;
        for f in 0..p.funcs.len() {
            n: str = nameOf(p.funcs.get(f).name);
            byName.put(n, f);
            byLabel.put(fnLabel(n), f);
        }
        globalAt: HashMap<str, long>;       // a global's name -> its index; and its label -> the same
        for g in 0..p.globals.len() {
            globalAt.put(nameOf(p.globals.get(g)), g);
            globalAt.put(globalSymbol(nameOf(p.globals.get(g))), g);
        }
        self.liveImage.clear();
        for g in 0..p.imageFirst.len() { self.liveImage.push(false); }
        self.liveStr.clear();
        g: long = 0;
        while (g < p.strings.len()) { self.liveStr.push(false); g = g + 1; }
        images: Vec<long>;
        vtImpl: HashMap<str, long>;
        for i in 0..gReg.implCount() {
            im: TraitImplDef = gReg.implAt(i);
            // The first impl under a label, as `emitVtables` writes it: two impls whose trait
            // references differ only in spelling share the label, and name their methods apart.
            if (!gReg.isGenericSym(im.structName) && gReg.findTraitSym(im.trait.name) >= 0
                && !vtImpl.has(implVtableName(im))) {
                vtImpl.put(implVtableName(im), i);
            }
        }
        work: Vec<long>;
        f: long = 0;
        while (f < p.funcs.len()) {
            fn: IRFunc = p.funcs.get(f);
            // `main` and the global initializer are the roots of a program. In a library every
            // `pub` function is a root too: it exists to be called by an object that is not this
            // one, and nothing here can see that call. Pruning the whole program is what keeps a
            // program's binary small (it took `vector` from 170,912 bytes to 66,896), so these
            // extra roots come only with the flag, never by default.
            if (fn.isMain || nameOf(fn.name) == "$globalInit") { work.push(f); }
            // The `@init`/`@fini` hooks `_start` calls, where `_start` is.
            else if (self.entryHere(p) && isHook(fn.name)) { work.push(f); }
            else if ((gEmitLibrary || gKlibMode) && fn.isPub) { work.push(f); }
            // A generic instance a package compiled is there for its dependents to link to, even
            // when every call to it here was inlined (and nothing here reaches the body).
            else if (gKlibMode && gInstanceFp.has(nameOf(fn.name))) { work.push(f); }
            f = f + 1;
        }
        // A package's storage is all exported: a dependent may read a global nothing in this
        // package does, and there has to be exactly one copy of it, here.
        if (gKlibMode) {
            g = 0;
            while (g < p.globals.len()) {
                n: str = nameOf(p.globals.get(g));
                if (!gUseSyms.has(globalSymbol(n))) { self.reachGlobal(p, n, &globalAt, &images); }
                g = g + 1;
            }
        }
        // Functions and images feed each other (a function reads a global whose image holds a
        // function's address), so both queues drain together.
        spillReached: bool = false;
        while (work.len() > 0 || images.len() > 0) {
            while (images.len() > 0) {
                im: long = images.pop();
                rf: long = p.imageRelocFirst.get(im);
                rc: long = p.imageRelocCount.get(im);
                for r in 0..rc {
                    k: RelocKind = p.relocKind.get(rf + r);
                    t: long = p.relocTarget.get(rf + r);
                    if (k == RelocKind.Fn)     { self.reachName(nameOf(t), &byName, &work); }
                    if (k == RelocKind.Vtable) { self.reachVtable(nameOf(t), &vtImpl, &byName, &work); }
                    if (k == RelocKind.Global) { self.reachGlobal(p, nameOf(t), &globalAt, &images); }
                    if (k == RelocKind.Block)  { self.reachImage(t, &images); }
                    if (k == RelocKind.Str)    { self.liveStr.set(t, true); }
                }
            }
            if (work.len() == 0) { continue; }
            f = work.pop();
            fn: IRFunc = p.funcs.get(f);
            if (self.live.has(nameOf(fn.name))) { continue; }
            self.live.put(nameOf(fn.name), true);
            at: long = fn.firstInstr;
            end: long = fn.firstInstr + fn.instrCount;
            while (at < end) {
                in: Instr = p.code.get(at);
                at = at + 1;
                // Already defined in another object: referenced but not walked into. What it
                // reaches is that object's business, and was kept when that object was built.
                if (in.op == IROp.Call && gUseSyms.has(fnLabelOf(in.name))) {
                    self.noteExtern(nameOf(in.name));
                    continue;
                }
                // A direct call names a function this program defines, or one declared without
                // a body that another object defines. Anything else is refused here, where the
                // callee still has the name the author wrote; let through, it would reach NASM,
                // which reports the mangled symbol at a line of the generated assembly.
                if (in.op == IROp.Call && !byName.has(nameOf(in.name))
                    && !isDeclaredExtern(p, in.name)) {
                    enterFnAtDef(fn.name);
                    failStr(format("cannot find function `{}`\nnote: it is called by `{}`, and nothing in the program defines it",
                                   nameOf(in.name), nameOf(fn.name)));
                }
                // A call into another object keeps nothing of this one alive, but the symbol has
                // to be declared to NASM: `liveExtern` is what the directive is written from.
                if (in.op == IROp.Call && isDeclaredExtern(p, in.name)) {
                    self.noteExtern(nameOf(in.name));
                }
                if (in.op == IROp.Call && !in.noReturn && !gIpraOff) {
                    // A call that returns, kept for `calleesFirst`.
                    k: long = self.reachCall(nameOf(in.name), &byName, &work);
                    if (k >= 0) { self.edgeFrom.push(f); self.edgeTo.push(k); }
                    continue;
                }
                if (in.op == IROp.Call || in.op == IROp.FnAddr) { self.reachName(nameOf(in.name), &byName, &work); continue; }
                if (in.op == IROp.VtableAddr) { self.reachVtable(nameOf(in.name), &vtImpl, &byName, &work); continue; }
                if (in.op == IROp.StrLitVal || in.op == IROp.StrAddr) { self.liveStr.set(in.imm, true); continue; }
                // A bounds check's report calls the `@spill` function (`emitBoundsFail`).
                if (in.op == IROp.Bounds && gSpillFn != NO_SYM && !spillReached) {
                    spillReached = true;
                    self.reachName(nameOf(gSpillFn), &byName, &work);
                    continue;
                }
                if (in.isGlobal && (in.op == IROp.Load || in.op == IROp.Store || in.op == IROp.AddrOf)) {
                    self.reachGlobal(p, nameOf(in.name), &globalAt, &images);
                    continue;
                }
                if (in.op == IROp.Asm) {
                    for q in 0..in.pieceCount {
                        if (p.asmKinds.get(in.firstPiece + q) == AsmKind.Text) {
                            self.reachSpelled(p, nameOf(p.asmText.get(in.firstPiece + q)), &byLabel, &work, &globalAt, &images);
                        }
                    }
                }
            }
        }
    }
    reachGlobal &self p:IRProgram n:str inout globalAt:HashMap<str, long> inout images:Vec<long> -> void {
        hit: Option<long> = globalAt.find(n);
        g: long = -1;
        match hit { Some(i) { g = i; } None { return; } }
        key: str = nameOf(p.globals.get(g));
        // Owned by another object. Referenced, never emitted, and its image is not walked: the
        // bytes live over there and so does everything they point at.
        if (gUseSyms.has(globalSymbol(key))) {
            if (!self.liveExternGlobal.has(globalSymbol(key))) {
                self.liveExternGlobal.put(globalSymbol(key), true);
                self.externGlobalOrder.push(globalSymbol(key));
            }
            return;
        }
        if (self.liveGlobal.has(key)) { return; }
        self.liveGlobal.put(key, true);
        if (p.globalImage.get(g) >= 0) { self.reachImage(p.globalImage.get(g), images); }
    }
    reachImage &self im:long inout images:Vec<long> -> void {
        if (self.liveImage.get(im)) { return; }
        self.liveImage.set(im, true);
        images.push(im);
    }
    // `reachName` for a direct call, answering the callee's index, or -1 for one in another object.
    reachCall &self n:str inout byName:HashMap<str, long> inout work:Vec<long> -> long {
        if (gUseSyms.has(fnLabel(n))) { self.noteExtern(n); return -1; }
        hit: Option<long> = byName.find(n);
        match hit { Some(f) { work.push(f); return f; } None { } }
        return -1;
    }
    reachName &self n:str inout byName:HashMap<str, long> inout work:Vec<long> -> void {
        // Defined in another object: referenced but not walked into. Every way of reaching a
        // function other than a direct call (a vtable slot, a taken address, a pointer the
        // evaluator laid into `.data`) comes through here, so this is where the check belongs.
        // Checked only at calls, a vtable could hold `dq mfn_string$String_display` with no
        // `extern` to say the symbol lives elsewhere.
        if (gUseSyms.has(fnLabel(n))) { self.noteExtern(n); return; }
        hit: Option<long> = byName.find(n);
        match hit { Some(f) { work.push(f); } None { } }
    }
    reachVtable &self label:str inout vtImpl:HashMap<str, long> inout byName:HashMap<str, long> inout work:Vec<long> -> void {
        if (self.liveVt.has(label)) { return; }
        self.liveVt.put(label, true);
        hit: Option<long> = vtImpl.find(label);
        i: long = -1;
        match hit { Some(v) { i = v; } None { return; } }
        im: TraitImplDef = gReg.implAt(i);
        t: TraitDef = gReg.traitDef(gReg.findTraitSym(im.trait.name));
        for k in 0..t.methodCount {
            self.reachName(nameOf(implMethodName(im, gReg.traitMethodAt(t, k).name)), byName, work);
        }
    }
    // A label spelled inside assembly text, such as `call mfn_x` or `[rel gbl_y]`, keeps what it
    // names alive.
    reachSpelled &self p:IRProgram text:str inout byLabel:HashMap<str, long> inout work:Vec<long>
                 inout globalAt:HashMap<str, long> inout images:Vec<long> -> void {
        if (strContains(text, "__heapCentral")) { self.needHeapCentral = true; }
        i: long = 0;
        while (i + 4 <= text.len) {
            rest: str = strSlice(text, i, text.len - i);
            isFn: bool = strStartsWith(rest, "mfn_");
            if (isFn || strStartsWith(rest, "gbl_")) {
                j: long = i;
                while (j < text.len && (isIdentPart(charAt(text, j)) || charAt(text, j) == '$' || charAt(text, j) == '.')) { j = j + 1; }
                label: str = strSlice(text, i, j - i);
                if (isFn) {
                    hit: Option<long> = byLabel.find(label);
                    match hit { Some(f) { work.push(f); } None { } }
                } else { self.reachGlobal(p, label, globalAt, images); }
                i = j;
            } else { i = i + 1; }
        }
    }

    // The cold half of every bounds check: report, then abort. One copy per program of each
    // report a check can reach.
    //
    // Hand-written because there is nothing to call: the output has to be freestanding, and a
    // program that indexes an array need not have included the standard library. It touches no
    // allocator and no buffered sink and writes straight to fd 2, because a failed bounds check is
    // exactly when the rest of the program's state stops being worth trusting.
    //
    // The one thing it does call is the program's `@spill` function, when it has one, before the
    // report: the bytes the program printed and still holds back for stdout (a pipe or a file)
    // would otherwise be lost, or land after the report that followed them. That function takes
    // no lock, and is called once: a check failing inside it reports without calling it again.
    //
    // Exits 134, the status of a process killed by SIGABRT, so a caller testing for a crash still
    // sees one.
    emitBoundsFail &self -> void {
        if (!self.needBounds) { return; }
        self.emitFailReport("__methBoundsFail", "__methBndHead", "__methBndMid");
        if ((self.needSlice & 2) != 0) { self.emitFailReport("__methRangeFail", "__methRngHead", "__methBndMid"); }
        if ((self.needSlice & 4) != 0) { self.emitFailReport("__methOrderFail", "__methStartHead", "__methOrdMid"); }
        if ((self.needSlice & 8) != 0) { self.emitFailReport("__methStartFail", "__methStartHead", "__methBndMid"); }

        // The `@spill` call, once. The report was called from wherever the check failed, so the
        // stack is aligned here for the call by hand; r12 to r15, which hold the report's numbers,
        // are callee-saved and come back as they were. Nothing returns to the failed check, so
        // nothing else needs keeping.
        if (self.spillHere()) {
            self.putLine("__methSpill:");
            self.putLine("cmp byte [rel __methSpilled], 0");
            self.putLine("jne .spilled");
            self.putLine("mov byte [rel __methSpilled], 1");
            self.putLine("push rbp");
            self.putLine("mov rbp, rsp");
            self.putLine("and rsp, -16");
            self.put("call ");
            self.putLine(fnLabelOf(gSpillFn));
            self.putLine("mov rsp, rbp");
            self.putLine("pop rbp");
            self.putLine(".spilled:");
            self.putLine("ret");
        }

        // write(2, rsi, rdx)
        self.putLine("__methBndPut:");
        self.putLine("mov eax, 1");
        self.putLine("mov edi, 2");
        self.putLine("syscall");
        self.putLine("ret");

        // rdi in decimal, to fd 2. Digits are built backwards into 32 bytes of stack, so this
        // allocates nothing. Signed, because a negative index is the common mistake and printing
        // it as an enormous unsigned number would hide exactly what went wrong.
        self.putLine("__methBndNum:");
        self.putLine("sub rsp, 32");
        self.putLine("lea rcx, [rsp + 32]");
        self.putLine("mov rax, rdi");
        self.putLine("xor r8, r8");
        self.putLine("test rax, rax");
        self.putLine("jns .bndpos");
        self.putLine("neg rax");
        self.putLine("mov r8d, 1");
        self.putLine(".bndpos:");
        self.putLine("mov r9d, 10");
        self.putLine(".bnddigit:");
        self.putLine("xor rdx, rdx");
        self.putLine("div r9");
        self.putLine("add rdx, 48");
        self.putLine("dec rcx");
        self.putLine("mov [rcx], dl");
        self.putLine("test rax, rax");
        self.putLine("jnz .bnddigit");
        self.putLine("test r8, r8");
        self.putLine("jz .bndunsigned");
        self.putLine("dec rcx");
        self.putLine("mov byte [rcx], 45");
        self.putLine(".bndunsigned:");
        self.putLine("lea rdx, [rsp + 32]");
        self.putLine("sub rdx, rcx");
        self.putLine("mov rsi, rcx");
        self.putLine("mov eax, 1");
        self.putLine("mov edi, 2");
        self.putLine("syscall");
        self.putLine("add rsp, 32");
        self.putLine("ret");
    }

    // Whether the reports call the `@spill` function: the program has one, and `markReachable`
    // reached it from a bounds check (here, or defined in another object).
    spillHere &self -> bool {
        if (gSpillFn == NO_SYM) { return false; }
        return self.live.has(nameOf(gSpillFn)) || self.liveExtern.has(nameOf(gSpillFn));
    }

    // `<label>:` with rdi = the index, rsi = the length and rdx:rcx = the {bytes, length} of a
    // `file:line`, or zero for none. Calls the `@spill` function if there is one (`__methSpill`),
    // then prints the head, the index, the middle, the length, then
    // ` at <where>` when there is a location, and a newline, and exits 134.
    emitFailReport &self label:str head:str mid:str -> void {
        self.put(label);
        self.putLine(":");
        self.putLine("mov r12, rdi");
        self.putLine("mov r13, rsi");
        self.putLine("mov r14, rdx");
        self.putLine("mov r15, rcx");
        if (self.spillHere()) { self.putLine("call __methSpill"); }
        self.emitPutText(head);
        self.putLine("mov rdi, r12");
        self.putLine("call __methBndNum");
        self.emitPutText(mid);
        self.putLine("mov rdi, r13");
        self.putLine("call __methBndNum");
        // The location, when the index came from a line someone wrote. A label of its own per
        // wording, so the two reports do not have to share a jump target.
        self.putLine("test r15, r15");
        self.putLine("jz .noloc");
        self.emitPutText("__methBndAt");
        self.putLine("mov rsi, r14");
        self.putLine("mov rdx, r15");
        self.putLine("call __methBndPut");
        self.putLine(".noloc:");
        self.putLine("lea rsi, [rel __methBndNl]");
        self.putLine("mov edx, 1");
        self.putLine("call __methBndPut");
        self.putLine("mov edi, 134");
        self.putLine("mov eax, 60");
        self.putLine("syscall");
    }
    emitPutText &self label:str -> void {
        self.put("lea rsi, [rel ");
        self.put(label);
        self.putLine("]");
        self.put("mov rdx, ");
        self.putNum(boundsText(label).len);
        self.putLine("");
        self.putLine("call __methBndPut");
    }

    // One label per file global, holding its value when the initializer was a constant and zeroed
    // otherwise. A zeroed global's initializer runs at program start, which is why a global may
    // still be built from any expression at all.
    emitData &self p:IRProgram -> void {
        self.putLine("section .data");
        // The static heap regions first, each in a 64 KiB-aligned section of its own (`emitBlocks`
        // says why).
        self.emitBlocks(p);
        // Back to `.data`. The regions' sections have names of their own, not `.data.something`,
        // because ld merges `.data.*` into `.data`, which would put the 64 KiB gap back inside it.
        // Everything below belongs in the ordinary `.data`.
        self.putLine("section .data");
        self.emitBoundsText();
        self.emitStrings(p);
        // The allocator's shared state: per-size-class central free lists and their locks, plus
        // the arena bump pointer. `stdlib/heap.k` reaches it from inline asm as
        // `[rel __heapCentral]`, so the back end has to put it there. Zero means unused. In a
        // build from packages it is defined once, by the object whose code names it (the
        // standard library's), and exported: every other object reaches the allocator through
        // that one's functions, and a second copy would be a second heap.
        if (!gKlibMode) { self.putLine("__heapCentral: times 1024 db 0"); }
        else if (self.needHeapCentral) {
            self.putLine("global __heapCentral");
            self.putLine("__heapCentral: times 1024 db 0");
        }
        i: long = 0;
        while (i < p.globals.len()) {
            if (!isVarGlobal(p.globals.get(i)) || !self.liveGlobal.has(nameOf(p.globals.get(i)))) { i = i + 1; continue; }
            self.put(globalSymbol(nameOf(p.globals.get(i))));
            if (p.globalImage.get(i) >= 0) {
                self.putLine(":");
                self.emitImage(p, p.globalImage.get(i));
            } else if (p.globalHasInit.get(i)) {
                self.put(": ");
                self.put(dataDirective(p.globalBytes.get(i)));
                self.put(" ");
                self.putNum(p.globalInits.get(i));
                self.putLine("");
            } else {
                self.put(": times ");
                self.putNum(p.globalBytes.get(i));
                self.putLine(" db 0");
            }
            i = i + 1;
        }
        self.emitVtables();
        self.emitConsts(p);
    }

    // A global not declared `var` is read-only, so it goes in `.rodata`. A write the checker could
    // not see (through a raw pointer to it in `unsafe` code) then faults instead of quietly
    // landing.
    emitConsts &self p:IRProgram -> void {
        any: bool = false;
        for i in 0..p.globals.len() {
            if (!isVarGlobal(p.globals.get(i)) && self.liveGlobal.has(nameOf(p.globals.get(i)))) {
                if (!any) { self.putLine("section .rodata"); any = true; }
                self.put(globalSymbol(nameOf(p.globals.get(i))));
                if (p.globalImage.get(i) >= 0) {
                    self.putLine(":");
                    self.emitImage(p, p.globalImage.get(i));
                } else if (p.globalHasInit.get(i)) {
                    self.put(": ");
                    self.put(dataDirective(p.globalBytes.get(i)));
                    self.put(" ");
                    self.putNum(p.globalInits.get(i));
                    self.putLine("");
                } else {
                    self.put(": times ");
                    self.putNum(p.globalBytes.get(i));
                    self.putLine(" db 0");
                }
            }
        }
    }

    // An image is rows of bytes, with one `dq` at each relocation naming what that word points at
    // (a string literal's bytes, another block, a global, a vtable or a function) plus the offset
    // into it. That is how a pointer computed at compile time points at the same `.data` a
    // mention in code would.
    emitImage &self p:IRProgram im:long -> void {
        first: long = p.imageFirst.get(im);
        count: long = p.imageCount.get(im);
        rf: long = p.imageRelocFirst.get(im);
        rc: long = p.imageRelocCount.get(im);
        at: long = 0;
        r: long = 0;
        while (at < count) {
            if (r < rc && p.relocOffset.get(rf + r) == at) {
                self.put("dq ");
                k: RelocKind = p.relocKind.get(rf + r);
                t: long = p.relocTarget.get(rf + r);
                if (k == RelocKind.Str)    { self.put(strBytesLabel(t)); }
                if (k == RelocKind.Block)  { self.put(blockLabel(t)); }
                if (k == RelocKind.Global) { self.put(globalSymbol(nameOf(t))); }
                if (k == RelocKind.Vtable) { self.put(nameOf(t)); }
                if (k == RelocKind.Fn)     { self.put(fnLabelOf(t)); }
                d: long = p.relocDelta.get(rf + r);
                if (d != 0) { self.put(" + "); self.putNum(d); }
                self.putLine("");
                at = at + 8;
                r = r + 1;
            } else {
                stopAt: long = count;
                if (r < rc) { stopAt = p.relocOffset.get(rf + r); }
                if (stopAt > at + 16) { stopAt = at + 16; }
                self.put("db ");
                for k in at..stopAt {
                    if (k > at) { self.put(", "); }
                    self.putNum(p.imageBytes.get(first + k) as long);
                }
                self.putLine("");
                at = stopAt;
            }
        }
    }

    // The heap blocks made at compile time. `free` on one of these must do nothing, and `free`
    // tells where a block came from by the word at its 64 KiB-aligned slab base. So the blocks
    // are laid out in regions of that alignment whose first word is 1000, the static marker
    // `stdlib/heap.k` checks for. A block that would not fit in what is left of a region goes at
    // the head of a fresh one instead. A block bigger than a region may still run past its end,
    // since only a block's start is ever handed to `free`.
    emitBlocks &self p:IRProgram -> void {
        used: long = 0;            // bytes of the current region already taken, 0 = no region
        self.heapRegions = 0;
        for i in 0..p.imageFirst.len() {
            if (p.imageIsBlock.get(i) && self.liveImage.get(i)) {
                size: long = p.imageCount.get(i);
                if (used == 0 || used + 16 + size > 65536) {
                    // A section of its own, whose alignment the linker meets when it places
                    // the section, rather than an `align` inside `.data`. An `align` costs
                    // nothing only while the regions sit at the head of the section; linked
                    // beside another object's `.data` they no longer do, and the gap becomes
                    // real (65 KB of zeros in a program whose regions held a few hundred bytes).
                    self.put("section .methheap");
                    self.putNum(self.heapRegions);
                    self.putLine(" progbits alloc write align=65536");
                    self.heapRegions = self.heapRegions + 1;
                    self.putLine("dq 1000, 0");
                    used = 16;
                }
                self.putLine("align 16");
                used = (used + 15) & ~15;
                self.put(blockLabel(i));
                self.putLine(":");
                self.emitImage(p, i);
                used = used + size;
            }
        }
    }

    // The fixed pieces of the bounds reports. Their lengths come from the text itself, so editing
    // one cannot leave a `mov rdx, <len>` counting the old one.
    emitBoundsText &self -> void {
        if (!self.needBounds) { return; }
        self.emitTextLabel("__methBndHead");
        self.emitTextLabel("__methBndMid");
        if ((self.needSlice & 2) != 0) { self.emitTextLabel("__methRngHead"); }
        if ((self.needSlice & 12) != 0) { self.emitTextLabel("__methStartHead"); }
        if ((self.needSlice & 4) != 0) { self.emitTextLabel("__methOrdMid"); }
        self.emitTextLabel("__methBndAt");
        // One label per place a check can fail, filled while the code was emitted.
        for i in 0..self.locs.len() {
            self.put(locLabel(i));
            self.put(": db ");
            self.emitBytes(nameOf(self.locs.get(i)));
            self.putLine("");
        }
        self.putLine("__methBndNl: db 10");
        // Set once the `@spill` function has been called, so a check failing inside it reports
        // without calling it again.
        if (self.spillHere()) { self.putLine("__methSpilled: db 0"); }
    }
    emitTextLabel &self label:str -> void {
        self.put(label);
        self.put(": db ");
        self.emitBytes(boundsText(label));
        self.putLine("");
    }

    // One table of addresses per implementation, in the trait's declaration order, which is the
    // order `methodSlot` indexes by, and need not be the order the impl block wrote them in.
    // Only the tables something reaches (`markReachable`): a table names every method of its
    // impl, so an unreached one would keep them all.
    emitVtables &self -> void {
        // Deduplicated by label, not by impl: two impls whose trait references differ only in how
        // the instantiation is spelled mangle to the same table name, and NASM refuses a label
        // defined twice. The label is the thing that has to be unique, so it is what is checked.
        done: HashMap<str, long>;
        i: long = 0;
        while (i < gReg.implCount()) {
            im: TraitImplDef = gReg.implAt(i);
            // A template implements nothing: its methods are patterns, not code. Only the stamped
            // instances have addresses, and monomorphization registered an impl for each.
            if (gReg.isGenericSym(im.structName)) { i = i + 1; continue; }
            at: long = gReg.findTraitSym(im.trait.name);
            if (at < 0) { i = i + 1; continue; }
            label: str = implVtableName(im);
            if (done.has(label) || !self.liveVt.has(label)) { i = i + 1; continue; }
            done.put(label, 1);
            if (gKlibMode) { gEmittedVtables.push(label); }
            t: TraitDef = gReg.traitDef(at);
            self.put(label);
            self.put(": dq ");
            for k in 0..t.methodCount {
                if (k > 0) { self.put(", "); }
                self.put(fnLabelOf(implMethodName(im, gReg.traitMethodAt(t, k).name)));
            }
            if (t.methodCount == 0) { self.put("0"); }
            self.putLine("");
            i = i + 1;
        }
    }

    // `_start` calls `main` and hands its return straight to the exit syscall, which is what makes
    // a program's exit code exactly what `main` returned.
    emitStart &self p:IRProgram -> void {
        self.putLine("global _start");
        self.putLine("_start:");
        // Every `@init` hook first, dependencies' before their dependents': before any startup
        // initializer, which may allocate (the heap's is one).
        for k in 0..gInitHooks.len() { self.callHook(p, gInitHooks.get(k)); }
        // Built from packages, every package that initializes something at startup has its own
        // initializer, and they run in dependency order, each before anything that can read
        // what it built.
        for k in 0..gStartInits.len() {
            self.put("call ");
            self.putLine(gStartInits.get(k));
        }
        own: str = nameOf(initFunctionName());
        if (self.hasFunction(p, own)) {
            self.put("call ");
            self.putLine(fnLabel(own));
        }
        if (self.mainWantsArgs(p)) { self.emitArgvSlice(); }
        self.put("call ");
        self.putLine(self.mainLabel(p));
        fini: bool = gFiniHooks.len() > 0;
        // The `@fini` hooks, with `main`'s result kept for the exit: pushed twice so the stack
        // stays 16-aligned for the call.
        if (fini) {
            self.putLine("push rax");
            self.putLine("push rax");
            self.putLine("call __kiln_fini");
            self.putLine("pop rax");
            self.putLine("pop rax");
        }
        self.putLine("mov rdi, rax");
        self.putLine("mov eax, 60");
        self.putLine("syscall");
        // What `_start` and the `exit` builtin call, from this object or another: every `@fini`
        // hook, the last module's first. Entered at a call, so the stack is 8 off alignment: one
        // push puts it right for the hooks' calls.
        if (gKlibMode) { self.putLine("global __kiln_fini"); }
        self.putLine("__kiln_fini:");
        if (fini) {
            self.putLine("push rbx");
            k: long = gFiniHooks.len();
            while (k > 0) {
                k = k - 1;
                self.callHook(p, gFiniHooks.get(k));
            }
            self.putLine("pop rbx");
        }
        self.putLine("ret");
    }

    // A call to a hook from `_start`: defined in this object, or (another package's) declared
    // `extern` where it is called.
    callHook &self p:IRProgram h:Sym -> void {
        lb: str = fnLabelOf(h);
        if (!self.hasFunction(p, nameOf(h)) || gUseSyms.has(lb)) {
            self.put("extern ");
            self.putLine(lb);
        }
        self.put("call ");
        self.putLine(lb);
    }

    mainWantsArgs &self p:IRProgram -> bool {
        for f in 0..p.funcs.len() {
            fn: IRFunc = p.funcs.get(f);
            if (fn.isMain) { return fn.wantsArgs; }
        }
        return false;
    }

    // `main args: ...str`. At entry the kernel has put argc at [rsp] and the argv pointers just
    // above it, as NUL-terminated C strings. A `str` is {ptr, len}, so each one's length has to be
    // measured; the array and its slice header are built on the stack, whose top is where the
    // callee's frame will start: below what is written here, so nothing is clobbered. The
    // reservation is a multiple of 16, which is what keeps rsp aligned.
    emitArgvSlice &self -> void {
        self.putLine("mov rax, [rsp]");          // argc
        self.putLine("lea rsi, [rsp + 8]");      // &argv[0]
        self.putLine("mov rbx, rax");
        self.putLine("shl rbx, 4");              // argc * sizeof(str)
        self.putLine("add rbx, 16");             // + the slice header
        self.putLine("sub rsp, rbx");
        self.putLine("xor rcx, rcx");
        self.putLine(".args_build:");
        self.putLine("cmp rcx, rax");
        self.putLine("jge .args_done");
        self.putLine("mov rdx, [rsi + rcx*8]");
        self.putLine("mov r8, rdx");
        self.putLine(".args_strlen:");
        self.putLine("cmp byte [r8], 0");
        self.putLine("je .args_strlen_done");
        self.putLine("inc r8");
        self.putLine("jmp .args_strlen");
        self.putLine(".args_strlen_done:");
        self.putLine("sub r8, rdx");
        self.putLine("mov r9, rcx");
        self.putLine("shl r9, 4");
        self.putLine("mov [rsp + r9], rdx");     // str[i].ptr
        self.putLine("mov [rsp + r9 + 8], r8");  // str[i].len
        self.putLine("inc rcx");
        self.putLine("jmp .args_build");
        self.putLine(".args_done:");
        self.putLine("mov r9, rax");
        self.putLine("shl r9, 4");
        self.putLine("lea r10, [rsp + r9]");
        self.putLine("mov [r10], rsp");          // header.ptr
        self.putLine("mov [r10 + 8], rax");      // header.len
        self.putLine("mov rax, r10");            // argument 0: the slice's address
    }

    // `main`'s label, or "" when the program defines none: a package build has an entry point
    // only when its package holds `main`.
    mainLabelOrEmpty &self p:IRProgram -> str {
        for f in 0..p.funcs.len() {
            fn: IRFunc = p.funcs.get(f);
            if (fn.isMain) { return fnLabelOf(fn.name); }
        }
        return "";
    }

    mainLabel &self p:IRProgram -> str {
        for f in 0..p.funcs.len() {
            fn: IRFunc = p.funcs.get(f);
            if (fn.isMain) { return fnLabelOf(fn.name); }
        }
        return "mfn_main";
    }

    // ─── one function ────────────────────────────────────────────────────────

    emitFunction &self p:IRProgram fn:IRFunc -> void {
        enterFnAtDef(fn.name);
        self.ra.allocate(p, fn);
        // `clear` walks the whole table, which the largest function so far has grown: a map that
        // big is replaced instead, or every function after it pays for that one.
        if (self.slots.cap() > 512) { self.slots = map![]; } else { self.slots.clear(); }
        // The callee-saved registers are pushed after `rbp` is set up, so they occupy the first
        // words below it, and the frame starts below them. Otherwise slot 1 would land on a saved
        // register, and `pop r12` would read back whatever the body had left in that slot.
        self.frame = 8 * self.savedCount();
        // A callee-saved `xmm` register this function writes is kept in its frame meanwhile.
        self.xmmSaveAt.clear();
        for x in REG_XMM12..REG_SLOTS {
            if (self.ra.usedCallee.get(x)) { self.frame = self.frame + 8; self.xmmSaveAt.push(self.frame); }
            else { self.xmmSaveAt.push(0); }
        }
        // Indexed by a temp's position within this function, like the allocator's own table. Sized
        // by `tempCount` alone, it would have a slot for every temp in the program, and each one
        // this function never mentions would come back SPILLED and take eight bytes of its frame.
        self.spillBase = fn.firstTemp;
        self.spillAt.clear();
        for i in 0..fn.tempCount - fn.firstTemp { self.spillAt.push(0); }

        // The parameters: the leading run of seed loads. A promoted one is moved by the prologue
        // straight to its temp's home, so its named slot is never written or read (promotion
        // turned every other access to the name into the temp) and gets no frame space.
        seeds: long = 0;
        while (seeds < fn.instrCount) {
            in: Instr = p.code.get(fn.firstInstr + seeds);
            if (in.op != IROp.Load || !in.paramSeed) { break; }
            seeds = seeds + 1;
        }
        self.seedDirect.clear();
        for i in 0..seeds {
            in: Instr = p.code.get(fn.firstInstr + i);
            self.seedDirect.push(in.promoted && in.dst != NO_TEMP && !byValueAggregate(in.kind));
        }
        if (self.addrTaken.len() > 0) { self.addrTaken.clear(); }
        for i in 0..fn.instrCount {
            ix: long = fn.firstInstr + i;
            if (p.code[ix].op == IROp.AddrOf && !p.code[ix].isGlobal && p.code[ix].name != NO_SYM) {
                self.addrTaken.put(p.code[ix].name as long, true);
            }
        }

        // Every named variable and every spilled temp needs a slot. Assigned before anything is
        // emitted, because the prologue has to know the frame size up front.
        self.frameless = false;
        self.assignSlots(p, fn, seeds);
        self.landing.clear();
        if (fn.holdsRecover) {
            for i in 0..fn.instrCount {
                if (p.code[fn.firstInstr + i].op == IROp.RecoverPush) {
                    self.landing.put(p.code[fn.firstInstr + i].name as long, p.code[fn.firstInstr + i].imm);
                }
            }
        }
        self.frameless = self.canOmitFrame(p, fn, seeds);
        self.frameSub = self.frameBytes(p, fn);

        // A library puts every function in a section of its own, so `ld --gc-sections` can drop
        // the ones the program never reaches. Without that, a library costs every binary its whole
        // exported surface (this one is 297 symbols, and it took a 58 KB program to 307 KB),
        // because the object cannot know which of them a consumer will call; only the linker
        // can. A program's own object does not need it: `markReachable` already kept only what
        // `main` reaches.
        //
        // The cold half of each bounds check is written after this function's `ret` and so lands
        // in the same section, which is what keeps it with the code that jumps to it.
        if (gEmitLibrary || gKlibMode) {
            self.put("section .text.");
            self.put(fnLabelOf(fn.name));
            self.putLine(" progbits alloc exec nowrite align=64");
        }
        // Every function starts on a 64-byte line. Where a function falls within one decides how
        // its code meets the front end's fetch and decoded-instruction windows: at 16-byte
        // alignment the same bytes of `fib` took anywhere from 1.73 to 2.72 G cycles as the code
        // before it grew, `collatz` 1.20 to 1.47, and `higher` 0.19 to 0.23. Aligned to the line,
        // a function's timing moves only when its own code does. The padding lies between
        // functions, after a `ret` or a jump, so it never runs; it costs 2% of this compiler's
        // text.
        self.putLine("align 64");
        // A generic instance's function, compiled here: exported under a name of this package's
        // own beside its local one, for a dependent to link to rather than compile again. Two
        // packages that each compile one never collide, and this package's own calls keep the
        // local label.
        if (gKlibMode && gInstanceFp.has(nameOf(fn.name))) {
            alias: str = instanceAlias(nameOf(fn.name));
            self.put("global ");
            self.putLine(alias);
            self.put(alias);
            self.putLine(":");
        }
        fnFrom: long = self.out.length();
        self.lineAt = fnFrom;
        self.relax.begin(fnFrom);
        self.relaxing = true;
        self.put(fnLabelOf(fn.name));
        self.putLine(":");
        self.cold.clear();
        self.coldAside.clear();
        bodyAt: long = self.emitGuard(p, fn, seeds);
        self.emitPrologue();
        self.emitSeeds(p, fn, seeds);

        // A `ret` that is the body's last instruction falls into the epilogue rather than jumping to it.
        lastReal: long = fn.instrCount - 1;
        while (lastReal >= 0 && p.code[fn.firstInstr + lastReal].op == IROp.Nop) { lastReal = lastReal - 1; }
        self.boundsN = 0;
        self.markRotations(p, fn, bodyAt);
        // The seeds are the prologue's, and a test the guard made is not made again: the body
        // starts after both.
        i: long = bodyAt;
        while (i < fn.instrCount) {
            in: Instr = p.code.get(fn.firstInstr + i);
            // A branch and the arms it chose between, as conditional moves (`markSelects`).
            if (self.selAt.get(i) >= 0) {
                r: SelRegion = self.sels.get(self.selAt.get(i));
                self.emitRegion(p, fn, r);
                i = r.end + 1;
                continue;
            }
            // A loop's jump back to its test, made the test itself (`markRotations`).
            if (in.op == IROp.Jmp && self.rotFrom.get(i) >= 0) {
                self.emitRotated(p, fn, i);
                i = i + 1;
                continue;
            }
            // A jump to a loop's last block, where `if`'s arms meet: that block and the loop's
            // test written here instead, then the way out for when the loop ends.
            if (in.op == IROp.Jmp && self.dupTo.get(i) >= 0) {
                l: long = self.dupTo.get(i);
                for m in self.latchAt.get(l) + 1..l {
                    if (p.code[fn.firstInstr + m].op != IROp.Nop) { self.emitInstr(p, fn, p.code.get(fn.firstInstr + m)); }
                }
                self.emitRotated(p, fn, l);
                exitAt: long = fn.firstInstr + self.rotFrom.get(l);
                self.put("jmp ");
                self.putLine(nameOf(p.code[exitAt].name));
                i = i + 1;
                continue;
            }
            // A check that jumps over its own panic (`if (i < len) goto ok; panic(...); ok:`) is
            // written the other way round: it jumps to the panic, which goes out of line past the
            // `ret` with the bounds failures, so the path that runs falls straight through. Only
            // the text moves and the register allocation is the IR's, which is why this is done
            // here in the emitter.
            if (in.op == IROp.Jcc && !isFloat(in.kind)) {
                e: long = self.coldRun(p, fn, i);
                if (e >= 0) {
                    j: long = i + 1;
                    while (p.code[fn.firstInstr + j].op == IROp.Nop) { j = j + 1; }
                    inv: Instr = in;
                    inv.cmpOp = negateCompare(in.cmpOp);
                    labeled: bool = p.code[fn.firstInstr + j].op == IROp.Label;
                    if (labeled) { inv.name = p.code[fn.firstInstr + j].name; }
                    else {
                        self.coldSeq = self.coldSeq + 1;
                        inv.name = internString(format(".CR{}", self.coldSeq));
                    }
                    self.emitInstr(p, fn, inv);
                    // The cold run is written into a buffer of its own; `relax` reads it with the
                    // rest of the cold text, after the `ret`.
                    hot: String = take(&self.out);
                    hotLine: long = self.lineAt;
                    self.relaxing = false;
                    self.lineAt = 0;
                    if (!labeled) { self.put(nameOf(inv.name)); self.putLine(":"); }
                    for k in j..e + 1 { self.storeBefore(k); self.emitInstr(p, fn, p.code.get(fn.firstInstr + k)); self.reloadAfter(k); }
                    text: String = take(&self.out);
                    self.out = take(&hot);
                    self.relaxing = true;
                    self.lineAt = hotLine;
                    self.coldAside.push(self.cold.length());
                    unsafe { self.cold.pushStr(text.view()); }
                    self.coldAside.push(self.cold.length());
                    i = e + 1;
                    continue;
                }
            }
            self.atLast = i == lastReal;
            self.storeBefore(i);
            self.emitInstr(p, fn, in);
            self.atLast = false;
            self.reloadAfter(i);
            if (self.rotLabel.get(i) != NO_SYM) {
                self.put(nameOf(self.rotLabel.get(i)));
                self.putLine(":");
            }
            i = i + 1;
        }

        self.put(".end");
        self.put(fnLabelOf(fn.name));
        self.putLine(":");
        self.emitEpilogue();
        // Past the `ret`: the cold halves of this function's bounds checks. None of them returns.
        // Neither does a cold run, so what either writes is nothing a caller sees (`coldAside`);
        // the rest of the cold text (an early return, a division's slow way) counts.
        coldAt: long = self.out.length();
        unsafe { self.put(self.cold.view()); }
        at: long = coldAt;
        for k in 0..self.coldAside.len() / 2 {
            a: long = coldAt + self.coldAside.get(2 * k);
            b: long = coldAt + self.coldAside.get(2 * k + 1);
            self.relax.text(&self.out, at, a);
            self.relax.aside = true;
            self.relax.text(&self.out, a, b);
            self.relax.aside = false;
            at = b;
        }
        self.relax.text(&self.out, at, self.out.length());
        self.cold.clear();
        self.coldAside.clear();
        // The jumps that reach their targets in two bytes, written so (`relax.k`).
        self.relaxing = false;
        self.relax.finish(&self.out);
        self.lineAt = self.out.length();
        if (!gIpraOff) { self.finishMask(p, fn); }
    }

    // Shrink-wrapping, for a function that begins by deciding whether it has anything to do:
    // `if (n < 2) { return n; }`, `if (p == null) { return; }`. That test and the return it
    // leads to are written before the prologue, reading each parameter where it arrived
    // (argument k in register k), so the early return pays for no frame, no saved register and
    // no parameter moves: `cmp rax, 2` / `jl` / `ret`. The return itself goes out of line, past
    // the function's `ret` with the cold paths, so the path that does the work falls through
    // into the prologue.
    //
    // What qualifies, from the instruction after the seeds: a few instructions that compute in
    // registers only (a constant, a copy, `+ - * & | ^` or a conversion of integers, a load from
    // a global or through a pointer), each reading parameters or what an earlier one computed,
    // then a branch on an integer comparison. One side of the branch must lead, through more of
    // the same, to a `return` of an integer or of nothing. A float, a parameter not promoted or
    // not in a register, a call, a store, a slot or a label stops it. Each value computed on the
    // way gets a caller-saved register no argument arrives in: the caller expects those
    // clobbered, and every argument must still be where it arrived when the test fails. None of
    // these instructions is written with `rax` or `rdx` as a scratch when its operands are in
    // registers, which is why the list is what it is.
    //
    // Done only when the body can then skip the test: what it computed is read nowhere else,
    // and when the early return is the fall-through, nothing else reaches it and the other
    // side's label follows it. The path that does the work then runs exactly the instructions it
    // ran before, the test moved above the prologue, and the early return runs only its own.
    // Returns where the body starts.
    emitGuard &self p:IRProgram fn:IRFunc seeds:long -> long {
        if (self.frameless && self.savedCount() == 0 && self.frameSub == 0) { return seeds; }
        // The parameters it may read, each in the register its argument arrives in.
        gT: Vec<Temp>; gR: Vec<long>;
        nInt: long = 0;
        for i in 0..seeds {
            in: Instr = p.code.get(fn.firstInstr + i);
            if (floatClass(in.kind, in.structName) > 0) { continue; }
            if (nInt < INT_ARG_REGS && in.promoted && in.dst != NO_TEMP && !byValueAggregate(in.kind)) {
                gT.push(in.dst);
                gR.push(nInt);
            }
            nInt = nInt + 1;
        }
        params: long = gT.len();
        pool: long = 0;
        gb: long = -1;
        i: long = seeds;
        while (i < fn.instrCount && i < seeds + GUARD_SPAN) {
            in: Instr = p.code.get(fn.firstInstr + i);
            if (in.op == IROp.Jz || (in.op == IROp.Jcc && !isFloat(in.kind))) {
                if (!guardHas(gT, in.a) || (in.op == IROp.Jcc && !in.bIsImm && !guardHas(gT, in.b))) { return seeds; }
                gb = i;
                break;
            }
            if (in.op != IROp.Nop) {
                if (!guardComputes(in, gT)) { return seeds; }
                pool = guardRegister(pool, nInt);
                if (pool < 0) { return seeds; }
                gT.push(in.dst);
                gR.push(callerSavedAt(pool));
                pool = pool + 1;
            }
            i = i + 1;
        }
        if (gb < 0) { return seeds; }
        br: Instr = p.code.get(fn.firstInstr + gb);

        // The side that returns: the fall-through first, then the branch's target.
        exitFall: bool = true;
        exitAt: long = gb + 1;
        held: long = gT.len();
        heldPool: long = pool;
        ret: long = -1;
        labelOnWay: bool = false;
        k: long = exitAt;
        while (k < fn.instrCount && k < exitAt + GUARD_SPAN && ret < 0) {
            in: Instr = p.code.get(fn.firstInstr + k);
            if (in.op == IROp.Label) { labelOnWay = true; }
            else if (in.op == IROp.Ret || in.op == IROp.RetVoid) {
                if (in.op == IROp.Ret && (!guardHas(gT, in.a) || floatClass(in.kind, in.structName) > 0
                                          || byValueAggregate(in.kind))) { break; }
                ret = k;
            } else if (in.op != IROp.Nop) {
                if (!guardComputes(in, gT)) { break; }
                pool = guardRegister(pool, nInt);
                if (pool < 0) { break; }
                gT.push(in.dst);
                gR.push(callerSavedAt(pool));
                pool = pool + 1;
            }
            k = k + 1;
        }
        // Skipping the test leaves the fall-through to run on into whatever follows the return,
        // which has to be the other side's label, and nothing else may jump into it.
        bodyAt: long = -1;
        if (ret >= 0 && !labelOnWay) {
            n: long = ret + 1;
            while (n < fn.instrCount && p.code[fn.firstInstr + n].op == IROp.Nop) { n = n + 1; }
            if (n < fn.instrCount && p.code[fn.firstInstr + n].op == IROp.Label && p.code[fn.firstInstr + n].name == br.name) {
                bodyAt = ret + 1;
            }
        }
        if (bodyAt < 0) {
            while (gT.len() > held) { gT.pop(); gR.pop(); }
            pool = heldPool;
            exitFall = false;
            ret = -1;
            exitAt = -1;
            for j in 0..fn.instrCount {
                if (p.code[fn.firstInstr + j].op == IROp.Label && p.code[fn.firstInstr + j].name == br.name) { exitAt = j + 1; break; }
            }
            if (exitAt < 0) { return seeds; }
            k = exitAt;
            while (k < fn.instrCount && k < exitAt + GUARD_SPAN && ret < 0) {
                in: Instr = p.code.get(fn.firstInstr + k);
                if (in.op == IROp.Ret || in.op == IROp.RetVoid) {
                    if (in.op == IROp.Ret && (!guardHas(gT, in.a) || floatClass(in.kind, in.structName) > 0
                                              || byValueAggregate(in.kind))) { return seeds; }
                    ret = k;
                } else if (in.op != IROp.Nop && in.op != IROp.Label) {
                    if (!guardComputes(in, gT)) { return seeds; }
                    pool = guardRegister(pool, nInt);
                    if (pool < 0) { return seeds; }
                    gT.push(in.dst);
                    gR.push(callerSavedAt(pool));
                    pool = pool + 1;
                }
                k = k + 1;
            }
            if (ret < 0) { return seeds; }
            // The target's block stays in the body, reached by whatever else jumps there.
            bodyAt = gb + 1;
        }
        // What the test computed, and the early return when it is skipped with it, must be read
        // nowhere the body still runs: the body no longer computes it.
        checkTo: long = held;
        if (exitFall) { checkTo = gT.len(); }
        for j in bodyAt..fn.instrCount {
            in: Instr = p.code.get(fn.firstInstr + j);
            if (in.op == IROp.Nop || in.op == IROp.Label) { continue; }
            if (guardReads(p, in, gT, params, checkTo)) { return seeds; }
        }

        // A value the guard computes is written before the prologue, so it may have no home in
        // the frame (`RegAlloc.homed`). Read nowhere past the guard, it crosses no call and has none.
        for g in 0..gT.len() { if (self.ra.isHomed(gT.get(g))) { return seeds; } }

        // Written with the guard's own registers, put back afterwards.
        was: Vec<long>;
        for g in 0..gT.len() {
            was.push(self.ra.regOf(gT.get(g)));
            self.ra.forceReg(gT.get(g), gR.get(g));
        }
        for j in seeds..gb {
            in: Instr = p.code.get(fn.firstInstr + j);
            if (in.op != IROp.Nop) { self.emitInstr(p, fn, in); }
        }
        self.coldSeq = self.coldSeq + 1;
        exitLabel: Sym = internString(format(".GX{}", self.coldSeq));
        jb: Instr = br;
        if (br.op == IROp.Jz) {
            jb = instr(IROp.Jcc);
            jb.a = br.a;
            jb.bIsImm = true;
            jb.bImm = 0;
            jb.kind = p.kindOf(br.a);
            jb.cmpOp = IROp.CmpEq;
            if (exitFall) { jb.cmpOp = IROp.CmpNe; }
        } else if (exitFall) { jb.cmpOp = negateCompare(br.cmpOp); }
        jb.name = exitLabel;
        self.emitInstr(p, fn, jb);
        // The early return, written after the `ret` with the cold paths.
        hot: String = take(&self.out);
        hotLine: long = self.lineAt;
        self.relaxing = false;
        self.lineAt = 0;
        self.put(nameOf(exitLabel));
        self.putLine(":");
        for j in exitAt..ret {
            in: Instr = p.code.get(fn.firstInstr + j);
            if (in.op != IROp.Nop && in.op != IROp.Label) { self.emitInstr(p, fn, in); }
        }
        rv: Instr = p.code.get(fn.firstInstr + ret);
        if (rv.op == IROp.Ret) {
            v: str = regName64(self.ra.regOf(rv.a));
            if (!(v == "rax")) {
                self.put("mov rax, ");
                self.putLine(v);
            }
        }
        self.putLine("ret");
        text: String = take(&self.out);
        self.out = take(&hot);
        self.relaxing = true;
        self.lineAt = hotLine;
        unsafe { self.cold.pushStr(text.view()); }
        for g in 0..gT.len() { self.ra.forceReg(gT.get(g), was.get(g)); }
        return bodyAt;
    }

    // A loop is lowered with its test at the top: `L: if (i >= n) goto X; body; goto L; X:`. Each
    // trip then runs the jump back as well as the test. Where the jump back is followed by X, the
    // test's own exit, it is written as the test turned round instead: `if (i < n) goto B`, B
    // just after the test at the top. That is the same decision on the same operands, so control
    // goes where it went, one jump sooner, and leaving the loop is falling through to X. The test
    // is an integer comparison or a test against zero; a float's is not turned round, since its
    // negation does not hold of a NaN, nor is a test whose other side is a cold path, which the
    // emitter moves out of line.
    //
    // What the header computes before its test (`while (i * i <= n)`, a length loaded for `i <
    // v.len`, a value the test is fused with) is written again before the turned test: a few
    // instructions the emitter writes the same wherever they stand (`repeatable`). Running them at
    // the jump back is what the jump did: it led straight to them, with every register as it was,
    // and they are written exactly as they are at the top.
    //
    // Where the loop's last block begins at a join (the arms of an `if` meeting just before the
    // jump back), each arm that jumps there gets a copy of that block and of the turned test,
    // then a jump to X for when the loop ends (`dupTo`), and the block itself is entered only by
    // falling in. A copy, again, runs what the jump led to in the state the jump left. Done when
    // the block is short and repeatable and each branch into it is a plain jump from inside the
    // loop; otherwise the jump back stays as it was.
    markRotations &self p:IRProgram fn:IRFunc from:long -> void {
        n: long = fn.instrCount;
        self.rotFrom.clear();
        self.rotLabel.clear();
        self.rotHead.clear();
        self.latchAt.clear();
        self.dupTo.clear();
        // The branches written as conditional moves first: they jump nowhere, so a label they
        // named is no longer a place paths meet.
        self.markSelects(p, fn, from);
        any: bool = false;
        for i in 0..n {
            self.rotFrom.push(-1);
            self.rotLabel.push(NO_SYM);
            self.rotHead.push(-1);
            self.latchAt.push(-1);
            self.dupTo.push(-1);
            if (p.code[fn.firstInstr + i].op == IROp.Jmp) { any = true; }
        }
        if (!any || gRotateOff) { return; }
        labels: HashMap<long, long>;
        refs: HashMap<long, long>;      // how many branches name each label
        jumps: HashMap<long, long>;     // ...and how many of them are plain jumps
        for i in 0..n {
            o: IROp = p.code[fn.firstInstr + i].op;
            nm: long = p.code[fn.firstInstr + i].name as long;
            if (o == IROp.Label) { labels.put(nm, i); }
            else if (isBranch(o) && !self.selIn.get(i)) {
                c: Option<long> = refs.find(nm);
                match c { Some(k) { refs.put(nm, k + 1); } None { refs.put(nm, 1); } }
                if (o == IROp.Jmp) {
                    c2: Option<long> = jumps.find(nm);
                    match c2 { Some(k) { jumps.put(nm, k + 1); } None { jumps.put(nm, 1); } }
                }
            }
        }
        for i in from..n {
            if (p.code[fn.firstInstr + i].op != IROp.Jmp) { continue; }
            h: long = -1;
            hit: Option<long> = labels.find(p.code[fn.firstInstr + i].name as long);
            match hit { Some(k) { h = k; } None { } }
            if (h < from || h >= i) { continue; }
            // The test, after what the header computes for it.
            t: long = h + 1;
            computed: long = 0;
            while (t < i && computed <= MAX_ROT_HEAD) {
                ot: IROp = p.code[fn.firstInstr + t].op;
                if (ot == IROp.Jcc || ot == IROp.Jz) { break; }
                if (ot != IROp.Nop) {
                    if (!repeatable(p.code.get(fn.firstInstr + t))) { computed = MAX_ROT_HEAD + 1; break; }
                    computed = computed + 1;
                }
                t = t + 1;
            }
            if (t >= i || computed > MAX_ROT_HEAD || self.selIn.get(t)) { continue; }
            to: IROp = p.code[fn.firstInstr + t].op;
            if (!((to == IROp.Jcc && !isFloat(p.code[fn.firstInstr + t].kind)) || to == IROp.Jz)) { continue; }
            if (to == IROp.Jcc && self.coldRun(p, fn, t) >= 0) { continue; }
            x: long = i + 1;
            while (x < n && p.code[fn.firstInstr + x].op == IROp.Nop) { x = x + 1; }
            if (x >= n || p.code[fn.firstInstr + x].op != IROp.Label
                || p.code[fn.firstInstr + x].name != p.code[fn.firstInstr + t].name) { continue; }
            // The jump back's own block: where it starts, and whether paths meet there.
            k: long = self.blockLabel(p, fn, i);
            // Where that block cannot be copied into each way in (one is a conditional branch,
            // `if` without `else`), the jump back is still turned round: every way in reaches
            // the turned test, which decides what the jump and the test at the top decided.
            if (k >= 0 && self.joinsAt(p, fn, k, refs)) {
                if (self.copiesTail(p, fn, k, i, h, refs, jumps)) {
                    for j in h..k {
                        if (p.code[fn.firstInstr + j].op == IROp.Jmp && p.code[fn.firstInstr + j].name == p.code[fn.firstInstr + k].name
                            && !self.selIn.get(j)) {
                            self.dupTo.set(j, i);
                        }
                    }
                } else if (gRotateJoinOff) { continue; }
            }
            if (self.rotLabel.get(t) == NO_SYM) {
                self.coldSeq = self.coldSeq + 1;
                self.rotLabel.set(t, internString(format(".LR{}", self.coldSeq)));
            }
            self.rotFrom.set(i, t);
            self.rotHead.set(i, h);
            self.latchAt.set(i, k);
        }
    }

    // The label the block ending at instruction `i` starts with, or -1 when it starts after a
    // branch, with no label of its own (only the fall-through reaches it).
    blockLabel &self p:IRProgram fn:IRFunc i:long -> long {
        k: long = i - 1;
        while (k >= 0) {
            o: IROp = p.code[fn.firstInstr + k].op;
            if (o == IROp.Label) { return k; }
            if (isTerminator(o)) { return -1; }
            k = k - 1;
        }
        return -1;
    }

    // Whether more than one way leads into the label at `k`: the branches that name it, and
    // falling into it.
    joinsAt &self p:IRProgram fn:IRFunc k:long refs:HashMap<long, long> -> bool {
        ways: long = 0;
        c: Option<long> = refs.find(p.code[fn.firstInstr + k].name as long);
        match c { Some(m) { ways = m; } None { } }
        b: long = k - 1;
        while (b >= 0 && p.code[fn.firstInstr + b].op == IROp.Nop) { b = b - 1; }
        if (b >= 0) {
            bo: IROp = p.code[fn.firstInstr + b].op;
            stops: bool = bo == IROp.Jmp || bo == IROp.Ret || bo == IROp.RetVoid
                          || (bo == IROp.Call && p.code[fn.firstInstr + b].noReturn);
            if (!stops) { ways = ways + 1; }
        }
        return ways > 1;
    }

    // Whether the block from label `k` to the jump back at `i` (header `h`) can be copied into
    // each jump that reaches it: a few repeatable instructions, no more than a few such jumps,
    // every branch to it one of them, each inside the loop above the block.
    copiesTail &self p:IRProgram fn:IRFunc k:long i:long h:long refs:HashMap<long, long> jumps:HashMap<long, long> -> bool {
        nm: long = p.code[fn.firstInstr + k].name as long;
        nr: long = 0;
        nj: long = 0;
        c: Option<long> = refs.find(nm);
        match c { Some(m) { nr = m; } None { } }
        c2: Option<long> = jumps.find(nm);
        match c2 { Some(m) { nj = m; } None { } }
        if (nj != nr || nj > MAX_TAIL_COPIES) { return false; }
        body: long = 0;
        for m in k + 1..i {
            if (p.code[fn.firstInstr + m].op == IROp.Nop) { continue; }
            if (!repeatable(p.code.get(fn.firstInstr + m))) { return false; }
            body = body + 1;
        }
        if (body > MAX_ROT_TAIL) { return false; }
        inside: long = 0;
        for j in h..k {
            if (p.code[fn.firstInstr + j].op == IROp.Jmp && p.code[fn.firstInstr + j].name as long == nm && !self.selIn.get(j)) { inside = inside + 1; }
        }
        return inside == nj;
    }

    // The jump back at `i` written as its loop's test (`markRotations`): what the header computes
    // for the test, then the test turned round.
    emitRotated &self p:IRProgram fn:IRFunc i:long -> void {
        t: long = self.rotFrom.get(i);
        for m in self.rotHead.get(i) + 1..t {
            if (p.code[fn.firstInstr + m].op != IROp.Nop) { self.emitInstr(p, fn, p.code.get(fn.firstInstr + m)); }
        }
        self.emitInstr(p, fn, self.rotatedTest(p, fn, t));
    }

    // The loop test at `t` turned round (`markRotations`): it goes back into the body, just past
    // the test at the top, when the test would not have left.
    rotatedTest &self p:IRProgram fn:IRFunc t:long -> Instr {
        test: Instr = p.code.get(fn.firstInstr + t);
        if (test.op == IROp.Jz) {
            j: Instr = instr(IROp.Jcc);
            j.a = test.a;
            j.bIsImm = true;
            j.bImm = 0;
            j.kind = p.kindOf(test.a);
            j.cmpOp = IROp.CmpNe;
            j.name = self.rotLabel.get(t);
            return j;
        }
        test.cmpOp = negateCompare(test.cmpOp);
        test.name = self.rotLabel.get(t);
        return test;
    }

    // Looks after the branch at `i` for a cold run: one that may start with a label, holds no
    // other label and no branch, and ends in a call that never returns, directly followed by the
    // branch's own target. Returns the index of that call, or -1.
    coldRun &self p:IRProgram fn:IRFunc i:long -> long {
        target: Sym = p.code[fn.firstInstr + i].name;
        j: long = i + 1;
        while (j < fn.instrCount && p.code[fn.firstInstr + j].op == IROp.Nop) { j = j + 1; }
        if (j >= fn.instrCount) { return -1; }
        // The run may start with a label of its own, or (when no branch names one) without.
        k: long = j;
        if (p.code[fn.firstInstr + j].op == IROp.Label) { k = j + 1; }
        while (k < fn.instrCount) {
            in: Instr = p.code.get(fn.firstInstr + k);
            if (in.op == IROp.Label || isTerminator(in.op)) { return -1; }
            if (in.op == IROp.Call && in.noReturn) {
                m: long = k + 1;
                while (m < fn.instrCount && p.code[fn.firstInstr + m].op == IROp.Nop) { m = m + 1; }
                if (m < fn.instrCount && p.code[fn.firstInstr + m].op == IROp.Label
                    && p.code[fn.firstInstr + m].name == target) { return k; }
                return -1;
            }
            k = k + 1;
        }
        return -1;
    }

    // What the prologue takes off `rsp` below its pushes, and the epilogue gives back.
    //
    // With a frame, the slots lie below `rbp` down to `frame` bytes, the saved registers' share
    // first, and `rbp` is 16-aligned (the call pushed eight and `push rbp` eight more). So `rsp`
    // ends at `rbp - alignUp16(frame)`, aligned at every call and below every slot, and the
    // pushes have already moved it past the saved registers.
    //
    // Without one, `rsp` is eight past alignment on entry and each push moves it eight more, so
    // it needs another eight when the count is even, and only when the body calls something
    // that may assume the ABI's alignment: a call, or an `asm` block, which may make one.
    frameBytes &self p:IRProgram fn:IRFunc -> long {
        saved: long = self.savedCount();
        if (!self.frameless) { return alignUp16(self.frame) - 8 * saved; }
        if ((saved % 2) == 1) { return 0; }
        for i in 0..fn.instrCount {
            o: IROp = p.code[fn.firstInstr + i].op;
            if (o == IROp.Call || o == IROp.CallIndirect || o == IROp.Asm) { return 8; }
        }
        return 0;
    }

    // Whether this function can do without a frame pointer: nothing in it is addressed through
    // `rbp`. That means no slot of any kind (the frame holds only the saved registers: no
    // variable, no spilled temp, no scratch block, no staged argument, no parked callee and no
    // saved `xmm` register), no parameter on the stack (read at `[rbp + 16 + 8k]`), and no `asm`
    // block that names `rbp` itself. The rest of the body reaches memory through registers, the
    // globals through `rip`, and the stack arguments of its calls through `rsp`, none of which
    // a frame pointer changes. `frameText` refuses a frame operand in such a function, so a slot
    // this misses is a compile-time error, never a wild store.
    canOmitFrame &self p:IRProgram fn:IRFunc seeds:long -> bool {
        if (self.frame != 8 * self.savedCount()) { return false; }
        ii: long = 0;
        fi: long = 0;
        for i in 0..seeds {
            in: Instr = p.code.get(fn.firstInstr + i);
            if (floatClass(in.kind, in.structName) > 0) { fi = fi + 1; } else { ii = ii + 1; }
        }
        if (ii > INT_ARG_REGS || fi > FLOAT_ARG_REGS) { return false; }
        for i in seeds..fn.instrCount {
            ix: long = fn.firstInstr + i;
            if (p.code[ix].op != IROp.Asm) { continue; }
            for k in 0..p.code[ix].pieceCount {
                at: long = p.code[ix].firstPiece + k;
                if (p.asmKinds.get(at) == AsmKind.Text && strContains(nameOf(p.asmText.get(at)), "rbp")) { return false; }
            }
        }
        return true;
    }

    // `push rbp` / `mov rbp, rsp` where there is a frame, the callee-saved registers this body
    // uses, the frame cut below them, and the callee-saved `xmm` registers into it. The pushes
    // come before `sub rsp`: pushing after it would shift `rsp` by eight per register, off the
    // alignment every call inside the body relies on.
    emitPrologue &self -> void {
        if (!self.frameless) {
            self.putLine("push rbp");
            self.putLine("mov rbp, rsp");
        }
        self.saveCalleeSaved(true);
        if (self.frameSub > 0) {
            self.put("sub rsp, ");
            self.putNum(self.frameSub);
            self.putLine("");
        }
        self.saveCalleeXmm(true);
    }

    // The prologue undone, in reverse, and the return.
    emitEpilogue &self -> void {
        self.saveCalleeXmm(false);
        if (self.frameSub > 0) {
            self.put("add rsp, ");
            self.putNum(self.frameSub);
            self.putLine("");
        }
        self.saveCalleeSaved(false);
        if (!self.frameless) { self.putLine("pop rbp"); }
        self.putLine("ret");
    }

    // The parameters, from where the caller left them to where the body reads them. A float
    // arrives in the next of the first eight `xmm` registers and any other in the next of the
    // first ten general registers, the two counted apart, and the rest on the stack above the
    // return address, eight bytes each in order: System V's rule, which `emitArgs` follows on the
    // calling side. A promoted parameter goes to its temp's home (a register, or the temp's spill
    // slot), any other to its named slot, and a by-value aggregate's address to its staging slot
    // until its bytes are copied.
    //
    // In four steps, each safe because of the ones before it:
    // - every destination in memory or in an `xmm` register is written first, straight from its
    //   argument register, while every argument is still where it arrived;
    // - the general registers are one parallel move, as a call's arguments are (`emitArgs`): a
    //   move is made once nothing still to be moved reads its destination, and a cycle is broken
    //   by an `xchg`. A source in an `xmm` register or on the stack never blocks;
    // - a stack parameter whose home is memory goes through `rax`, which by then no longer holds
    //   the first argument (and no temp lives in it here);
    // - last, each by-value aggregate is copied from the caller's object into its own slot through
    //   `rax` and `rdx`, which hold no parameter (`repMovs` gives back `rsi`, `rdi` and `rcx`).
    //
    // A parameter whose temp nothing reads is not moved at all. That is not only a saving: its
    // range ends at its own seed, so the allocator may have given its register to the next
    // parameter's temp, and moving it there would overwrite that one.
    emitSeeds &self p:IRProgram fn:IRFunc seeds:long -> void {
        ii: long = 0;
        fi: long = 0;
        si: long = 0;
        // The parallel move: each destination register, the argument register it reads (-1 for
        // none), and otherwise the operand it reads, an `xmm` register (`movq`) or a stack slot.
        rd: Vec<long>; rs: Vec<long>; rt: Vec<str>; rx: Vec<bool>;
        stackFrom: Vec<str>; stackTo: Vec<str>;
        for i in 0..seeds {
            in: Instr = p.code.get(fn.firstInstr + i);
            fl: bool = floatClass(in.kind, in.structName) > 0;
            src: long = -1;
            from: str = "";
            inXmm: bool = false;
            if (fl && fi < FLOAT_ARG_REGS) { from = xmmArgName(fi); inXmm = true; fi = fi + 1; }
            else if (!fl && ii < INT_ARG_REGS) { src = ii; ii = ii + 1; }
            else { from = stackParamText(si); si = si + 1; }
            dest: str = "";
            toXmm: bool = false;
            if (self.seedDirect.get(i)) {
                if (!self.ra.liveAfter(in.dst, i)) { continue; }
                r: long = self.ra.regOf(in.dst);
                if (r != SPILLED && !isXmm(r)) {
                    if (r != src) { rd.push(r); rs.push(src); rt.push(from); rx.push(inXmm); }
                    continue;
                }
                if (r != SPILLED) { dest = regName64(r); toXmm = true; } else { dest = self.place(in.dst); }
            } else if (byValueAggregate(in.kind)) { dest = self.argSlot(i); }
            else {
                dest = self.slotOf(in.name);
                // The parameter lives in its slot, but its seed's temp can still be read: a later
                // load of the slot that `flow.k` saw holds the seed's value reads the temp. It is
                // filled as a promoted seed's is, besides the slot.
                if (in.dst != NO_TEMP && self.ra.liveAfter(in.dst, i)) {
                    r: long = self.ra.regOf(in.dst);
                    if (r != SPILLED && !isXmm(r) && r != src) { rd.push(r); rs.push(src); rt.push(from); rx.push(inXmm); }
                    else if (r == SPILLED || isXmm(r)) {
                        tdest: str = self.place(in.dst);
                        if (r != SPILLED) { tdest = regName64(r); }
                        if (src >= 0) {
                            self.put("mov "); self.put(tdest); self.put(", "); self.putLine(regName(src));
                        } else if (inXmm || r != SPILLED) {
                            self.put("movq "); self.put(tdest); self.put(", "); self.putLine(from);
                        } else { stackFrom.push(from); stackTo.push(tdest); }
                    }
                }
            }
            if (src >= 0) {
                self.put("mov ");
                self.put(dest);
                self.put(", ");
                self.putLine(regName(src));
            } else if (inXmm || toXmm) {
                // An `xmm` argument into memory or a register, or a stack slot into an `xmm`
                // register: one `movq` either way.
                self.put("movq ");
                self.put(dest);
                self.put(", ");
                self.putLine(from);
            } else {
                stackFrom.push(from);
                stackTo.push(dest);
            }
        }
        while (rd.len() > 0) {
            moved: bool = false;
            m: long = 0;
            while (m < rd.len()) {
                d: long = rd.get(m);
                busy: bool = false;
                for j in 0..rs.len() { if (rs.get(j) == d) { busy = true; } }
                if (busy) { m = m + 1; continue; }
                if (rx.get(m)) { self.put("movq "); } else { self.put("mov "); }
                self.put(regName64(d));
                self.put(", ");
                if (rs.get(m) >= 0) { self.putLine(regName(rs.get(m))); } else { self.putLine(rt.get(m)); }
                dropSeedMove(&rd, &rs, &rt, &rx, m);
                moved = true;
            }
            if (moved) { continue; }
            // Every move left reads another's destination, so each reads a register and they form
            // cycles: break one at the first move, whose value the exchange puts in place, and
            // send whatever read either register to where its value went.
            d: long = rd.get(0);
            sr: long = rs.get(0);
            self.put("xchg ");
            self.put(regName64(d));
            self.put(", ");
            self.putLine(regName64(sr));
            dropSeedMove(&rd, &rs, &rt, &rx, 0);
            for j in 0..rs.len() {
                if (rs.get(j) == d) { rs.set(j, sr); }
                else if (rs.get(j) == sr) { rs.set(j, d); }
            }
            m2: long = 0;
            while (m2 < rd.len()) {
                if (rs.get(m2) == rd.get(m2)) { dropSeedMove(&rd, &rs, &rt, &rx, m2); } else { m2 = m2 + 1; }
            }
        }
        for k in 0..stackFrom.len() {
            self.put("mov rax, ");
            self.putLine(stackFrom.get(k));
            self.put("mov ");
            self.put(stackTo.get(k));
            self.putLine(", rax");
        }
        for i in 0..seeds {
            in: Instr = p.code.get(fn.firstInstr + i);
            if (gSinkHomesOff && in.dst != NO_TEMP && self.ra.isHomed(in.dst) && self.ra.liveAfter(in.dst, i)) { self.homeMove(in.dst, true); }
        }
        for i in 0..seeds {
            in: Instr = p.code.get(fn.firstInstr + i);
            if (byValueAggregate(in.kind)) {
                self.put("mov rdx, ");
                self.putLine(self.argSlot(i));
                self.copyFromPointer(self.slotOffsetOf(in.name), in.imm);
            }
        }
    }

    // How many callee-saved registers this function's prologue pushes.
    savedCount &self -> long {
        n: long = 0;
        for i in 0..CALLEE_SAVED_COUNT {
            if (self.ra.usedCallee.get(calleeSavedAt(i))) { n = n + 1; }
        }
        return n;
    }

    // The callee-saved `xmm` registers this function uses, into their frame slots on the way in
    // and back on the way out: the low eight bytes, all a scalar float occupies.
    saveCalleeXmm &self entering:bool -> void {
        for x in REG_XMM12..REG_SLOTS {
            off: long = self.xmmSaveAt.get(x - REG_XMM12);
            if (off == 0) { continue; }
            self.put("movq ");
            if (entering) { self.put(self.frameText(off)); self.put(", "); self.putLine(regName64(x)); }
            else { self.put(regName64(x)); self.put(", "); self.putLine(self.frameText(off)); }
        }
    }

    // Push on the way in, pop on the way out: in reverse, so the frame unwinds correctly.
    saveCalleeSaved &self entering:bool -> void {
        for i in 0..CALLEE_SAVED_COUNT {
            r: long = calleeSavedAt(i);
            k: long = r;
            if (!entering) { k = calleeSavedAt(CALLEE_SAVED_COUNT - 1 - i); }
            if (self.ra.usedCallee.get(k)) {
                if (entering) { self.put("push "); } else { self.put("pop "); }
                self.putLine(regName64(k));
            }
        }
    }

    // Named variables first, then spill slots. A scalar slot is eight bytes whatever its declared
    // width (a narrower value is stored extended, and one size keeps the offsets simple) but an
    // aggregate needs its whole block, because its fields are addressed at offsets inside it.
    assignSlots &self p:IRProgram fn:IRFunc seeds:long -> void {
        // Read in place, and the slots keyed by the name's number: a copy of every instruction
        // and a string hash per named access were most of what this cost. A parameter the
        // prologue moves straight to its temp (`seedDirect`) names its slot only in its seed.
        for i in 0..fn.instrCount {
            ix: long = fn.firstInstr + i;
            o: IROp = p.code[ix].op;
            if (i < seeds && self.seedDirect.get(i)) { continue; }
            if ((o == IROp.Load || o == IROp.Store || o == IROp.AddrOf) && !p.code[ix].isGlobal) {
                nm: Sym = p.code[ix].name;
                if (nm != NO_SYM && !self.slots.has(nm as long)) {
                    self.frame = self.frame + alignUp8(p.fnSlotBytesOf(fn.name, nm));
                    self.slots.put(nm as long, self.frame);
                }
            }
            // An `asm` block's `out` names a slot even when nothing reads it afterwards (a
            // `syscall` builtin's dropped result, whose load the optimizer removed). Without a
            // slot here the store would land at `[rbp - 0]`, over the saved frame pointer.
            if (o == IROp.Asm) {
                for k in 0..p.code[ix].pieceCount {
                    at: long = p.code[ix].firstPiece + k;
                    nm: Sym = p.asmNames.get(at);
                    if (p.asmKinds.get(at) == AsmKind.Out && nm != NO_SYM && !self.slots.has(nm as long)) {
                        self.frame = self.frame + alignUp8(p.fnSlotBytesOf(fn.name, nm));
                        self.slots.put(nm as long, self.frame);
                    }
                }
            }
        }
        // Scratch space for aggregate results, one block per call site that needs one. `AggSlot`
        // names a position in this list, not a size, which is why splicing a body elsewhere has
        // to offset those indices.
        //
        // The list is program-wide, so only the entries this function's own instructions name
        // take frame space. Reserving all of them would give every function, however small, a
        // frame as big as every aggregate in the program put together (58 KB for a two-line
        // accessor), and anything recursive would run out of stack.
        //
        // Which entries this function has placed is kept as a stamp per entry (`aggFn`). Clearing
        // and refilling the list for each function would walk the whole program's list once per
        // function emitted.
        self.fnSeq = self.fnSeq + 1;
        while (self.aggAt.len() < p.aggSlots.len()) { self.aggAt.push(0); self.aggFn.push(0); }
        for i in 0..fn.instrCount {
            ix: long = fn.firstInstr + i;
            if (p.code[ix].op != IROp.AggSlot && p.code[ix].op != IROp.RecoverPush) { continue; }
            s: long = p.code[ix].imm;
            if (self.aggFn.get(s) != self.fnSeq) {
                self.frame = self.frame + alignUp8(p.aggSlots.get(s));
                self.aggAt.set(s, self.frame);
                self.aggFn.set(s, self.fnSeq);
            }
        }

        // One slot for the callee of an indirect call. It has to be parked somewhere before the
        // argument registers are written, because argument `k` goes in register `k` and a callee
        // sitting in one of those would be overwritten before it could be called. Only a
        // function that makes such a call has it.
        indirect: bool = false;
        for i in 0..fn.instrCount { if (p.code[fn.firstInstr + i].op == IROp.CallIndirect) { indirect = true; } }
        if (indirect) {
            self.frame = self.frame + 8;
            self.calleeAt = self.frame;
        }

        // Where the prologue parks a by-value aggregate parameter's address while the argument
        // registers are drained (a call's arguments go straight to their registers, `emitArgs`):
        // a slot per parameter up to the last such one.
        self.argAt.clear();
        widest: long = 0;
        for i in 0..fn.instrCount {
            ix: long = fn.firstInstr + i;
            if (p.code[ix].op != IROp.Load || !p.code[ix].paramSeed) { break; }
            if (byValueAggregate(p.code[ix].kind)) { widest = i + 1; }
        }
        for i in 0..widest {
            self.frame = self.frame + 8;
            self.argAt.push(self.frame);
        }

        // Spill slots for this function's temps only; one for every temp in the program would make
        // a frame grow with the program rather than with the function. A temp the allocator left
        // without a register but that can be computed again where it is read
        // (`RegAlloc.markRemat`) takes no slot. Instead, the operand it is read as is kept here.
        self.rematText.clear();
        self.rematVal.clear();
        self.rematBase.clear();
        self.rematOff.clear();
        t: Temp = fn.firstTemp;
        while (t < fn.tempCount) {
            rk: long = self.ra.rematOf(t);
            txt: str = "";
            val: long = 0;
            rb: str = "";
            ro: long = 0;
            if (rk != REMAT_NONE) {
                d: Instr = p.code.get(fn.firstInstr + self.ra.rematAt(t));
                if (rk == REMAT_CONST) { txt = self.numText(d.imm); val = d.imm; }
                else if (rk == REMAT_ADDR) {
                    txt = self.placeOfName(d);
                    if (d.isGlobal) { rb = self.relBase(d.name); }
                    else { rb = "rbp"; ro = self.slotOffsetOf(d.name); }
                }
                else if (rk == REMAT_AGG) { txt = self.frameText(self.aggAt.get(d.imm)); rb = "rbp"; ro = self.aggAt.get(d.imm); }
                else { txt = self.relOperand(strConstLabel(d.imm)); }
            } else if ((self.ra.regOf(t) == SPILLED || self.ra.isHomed(t)) && self.ra.hasRange(t) && !self.ra.isFused(t)) {
                // A temp no instruction of this function names (one the optimizer left behind
                // with its last use) has no register, and needs no slot either.
                self.frame = self.frame + 8;
                self.spillAt.set(t - self.spillBase, self.frame);
            }
            self.rematText.push(txt);
            self.rematVal.push(val);
            self.rematBase.push(rb);
            self.rematOff.push(ro);
            t = t + 1;
        }
    }

    // `size` bytes from [rdx] into the frame block that starts at `[rbp - off]`, eight at a
    // time through the scratch. Every aggregate here is built of whole words and its storage is
    // rounded up to one, so there is no tail.
    copyFromPointer &self off:long size:long -> void {
        if (size > UNROLL_COPY_BYTES) {
            self.put("lea rax, [rbp - ");
            self.putNum(off);
            self.putLine("]");
            self.repMovs(size);
            return;
        }
        o: long = 0;
        while (o < size) {
            self.put("mov rax, [rdx");
            if (o != 0) { self.put(" + "); self.putNum(o); }
            self.putLine("]");
            self.put("mov [rbp - ");
            self.putNum(off - o);
            self.putLine("], rax");
            o = o + 8;
        }
    }

    // A named variable's offset from rbp, as a number: for the sites that have to address inside
    // its block rather than at its start.
    slotOffsetOf &self name:Sym -> long {
        hit: Option<long> = self.slots.find(name as long);
        match hit { Some(o) { return o; } None { } }
        return 0;
    }

    // Where that callee is parked, as an operand.
    calleeSlot &self -> str {
        s: String;
        s.pushStr("[rbp - ");
        s.pushLong(self.calleeAt);
        s.push(']');
        return keepString(s);
    }

    // Each string literal twice over: the bytes, and a 16-byte {ptr, len} pair pointing at them.
    // The pair is what a `str` value is, which is why a literal can be passed and stored like any
    // other 16-byte aggregate.
    emitStrings &self p:IRProgram -> void {
        i: long = 0;
        while (i < p.strings.len()) {
            if (!self.liveStr.get(i)) { i = i + 1; continue; }
            text: str = nameOf(p.strings.get(i));
            self.put(strBytesLabel(i));
            self.put(": db ");
            n: long = self.emitBytes(text);
            if (n == 0) { self.put("0"); }
            self.putLine("");
            self.put(strConstLabel(i));
            self.put(": dq ");
            self.put(strBytesLabel(i));
            self.put(", ");
            self.putNum(n);
            self.putLine("");
            i = i + 1;
        }
    }

    // The literal's bytes, with escapes resolved. Returns how many there are, which is the `len`
    // half of the fat pointer.
    emitBytes &self text:str -> long {
        n: long = 0;
        i: long = 0;
        while (i < text.len) {
            c: long = charAt(text, i);
            if (c == 92 && i + 1 < text.len) {
                i = i + 1;
                c = escapeByte(charAt(text, i));
            }
            if (n > 0) { self.put(", "); }
            self.putNum(c);
            n = n + 1;
            i = i + 1;
        }
        return n;
    }

    // Where a named variable lives. A global is reached through its own label, RIP-relative, so
    // the code is position-independent and needs no relocation at load time.
    placeOfName &self in:Instr -> str {
        if (in.isGlobal) {
            hit: Option<str> = self.globalText.find(in.name as long);
            match hit { Some(t) { return t; } None { } }
            s: String;
            s.pushStr("[rel ");
            s.pushStr(globalSymbol(nameOf(in.name)));
            s.push(']');
            out: str = "";
            out = keepString(s);
            self.globalText.put(in.name as long, out);
            return out;
        }
        return self.slotOf(in.name);
    }

    slotOf &self name:Sym -> str {
        hit: Option<long> = self.slots.find(name as long);
        off: long = 0;
        match hit { Some(o) { off = o; } None { } }
        return self.frameText(off);
    }

    // `lea <dst>, <operand>`, straight into the destination register when there is one.
    //
    // This serves all five instructions that produce an address. Computing into `rax` and copying
    // out cost three instructions to take one address in the hottest loop of the benchmark suite
    // (`lea rax, [rbp-104]` / `mov rbx, rax` / `mov rax, rbx`). `lea` reads only its base
    // register (`rbp` or `rip`), never its destination, so writing the destination directly can
    // destroy nothing the instruction still needs. A spilled destination still goes through the
    // scratch, because `lea` cannot write to memory.
    leaInto &self dst:Temp operand:str -> void {
        r: long = self.ra.regOf(dst);
        if (r != SPILLED) {
            self.put("lea ");
            self.put(regName64(r));
            self.put(", ");
            self.putLine(operand);
            return;
        }
        self.put("lea rax, ");
        self.putLine(operand);
        self.put("mov ");
        self.put(self.place(dst));
        self.putLine(", rax");
    }

    // Whether `t` has no home and is computed again wherever it is read.
    isRemat &self t:Temp -> bool {
        return t != NO_TEMP && self.ra.rematOf(t) != REMAT_NONE;
    }

    // Compute a rematerialized temp into register `r`: its constant, or the address it holds.
    // `mov`, never `xor`: it may stand between a comparison and the jump that reads its flags.
    materialize &self t:Temp r:long -> void {
        if (self.ra.rematOf(t) == REMAT_CONST) { self.movImm(r, self.rematVal.get(t - self.spillBase)); return; }
        self.put("lea ");
        self.put(regName64(r));
        self.put(", ");
        self.putLine(self.rematText.get(t - self.spillBase));
    }

    // `mov r, v` in the fewest bytes: NASM at -O1 writes every `mov r64, imm` with all eight
    // bytes of the immediate (ten in all). A value in 0..2^32-1 goes through the 32-bit register,
    // which zero-extends into the whole one (five bytes, six past `rdi`), and a negative one down
    // to -2^31 as the sign-extended 32-bit immediate (seven). Either way `r` ends up holding the
    // same value.
    movImm &self r:long v:long -> void {
        self.put("mov ");
        if (v >= 0 && v <= 4294967295) {
            self.put(regNameSized(r, 4));
            self.put(", ");
        } else if (v < 0 && v >= 0 - 2147483648) {
            self.put(regName64(r));
            self.put(", dword ");
        } else {
            self.put(regName64(r));
            self.put(", ");
        }
        self.putNum(v);
        self.putLine("");
    }

    // Where a temp lives: its register, or its spill slot.
    place &self t:Temp -> str {
        if (t == NO_TEMP) { return "rax"; }      // a missing operand: nothing sensible to name
        r: long = self.ra.regOf(t);
        if (r != SPILLED) { return regName64(r); }
        // A temp computed again where it is read has no slot: every read asks `isRemat` first.
        if (self.isRemat(t)) { fail("internal compiler error: a rematerialized temp was read as if it had a stack slot"); }
        return self.frameText(self.spillAt.get(t - self.spillBase));
    }

    // `rel <symbol>` for a global, the base of an addressing mode a displacement may follow,
    // built once per global and kept.
    relBase &self name:Sym -> str {
        hit: Option<str> = self.relBaseText.find(name as long);
        match hit { Some(t) { return t; } None { } }
        s: String;
        s.pushStr("rel ");
        s.pushStr(globalSymbol(nameOf(name)));
        out: str = "";
        out = keepString(s);
        self.relBaseText.put(name as long, out);
        return out;
    }

    // `[rel <label>]`, built once per label and kept.
    relOperand &self label:str -> str {
        hit: Option<str> = self.relText.find(label);
        match hit { Some(t) { return t; } None { } }
        s: String;
        s.pushStr("[rel ");
        s.pushStr(label);
        s.push(']');
        out: str = "";
        out = keepString(s);
        self.relText.put(keep(label), out);
        return out;
    }

    // `[rbp - N]`, built once per distinct offset and kept.
    //
    // This is asked for several times per instruction (once for every operand that lives in a
    // frame slot). Building a `String` and interning it each time costs an allocation, a hash and
    // a map lookup to produce one of a few hundred distinct strings, hundreds of thousands of
    // times a build. An offset is a small multiple of eight, so the cache is a vector indexed by
    // it and the answer costs one bounds-checked read. The text does not depend on which
    // function is being emitted (an offset from `rbp` means the same thing in all of them), so it
    // is never invalidated.
    // `RecoverPush`: the record a `raise` resumes from, in its frame slot (the layout is
    // `stdlib::recover`'s): the handler's address, rsp and rbp as they are here, and r12 to r15
    // and the low half of xmm12 to xmm14. Those are callee-saved between Kiln functions, and the
    // frames a `raise` abandons never put back what they saved of them, so the landing does. A
    // register this function saved itself gets its own value back, and its epilogue restores the
    // caller's; one it never touches still holds the caller's value here.
    emitRecoverPush &self in:Instr -> void {
        at: long = self.aggAt.get(in.imm);
        self.put("lea rax, ");
        self.putLine(self.relOperand(nameOf(in.name)));
        self.putRecordStore(at - RECORD_RESUME, "mov", "rax");
        self.putRecordStore(at - RECORD_RSP, "mov", "rsp");
        self.putRecordStore(at - RECORD_RBP, "mov", "rbp");
        for k in 0..4 { self.putRecordStore(at - RECORD_GPRS - 8 * k, "mov", regName64(REG_R12 + k)); }
        for k in 0..3 { self.putRecordStore(at - RECORD_XMMS - 8 * k, "movq", regName64(REG_XMM12 + k)); }
    }
    putRecordStore &self off:long op:str reg:str -> void {
        self.put(op);
        self.put(" ");
        self.put(self.frameText(off));
        self.put(", ");
        self.putLine(reg);
    }

    // A `recover` handler's label, where a `raise` arrives with rsp and rbp put back: the
    // registers the record kept are restored before the handler runs. Nothing the handler reads
    // is in a register (the allocator keeps what is live into a handler in the frame).
    emitLanding &self name:Sym -> void {
        hit: Option<long> = self.landing.find(name as long);
        slot: long = -1;
        match hit { Some(s) { slot = s; } None { return; } }
        at: long = self.aggAt.get(slot);
        for k in 0..4 {
            self.put("mov ");
            self.put(regName64(REG_R12 + k));
            self.put(", ");
            self.putLine(self.frameText(at - RECORD_GPRS - 8 * k));
        }
        for k in 0..3 {
            self.put("movq ");
            self.put(regName64(REG_XMM12 + k));
            self.put(", ");
            self.putLine(self.frameText(at - RECORD_XMMS - 8 * k));
        }
    }

    frameText &self off:long -> str {
        if (self.frameless) { fail("internal compiler error: a frame operand in a function emitted without a frame"); }
        i: long = off / 8;
        if (off < 0 || (off % 8) != 0) { return self.frameSlow(off); }
        while (self.frameCache.len() <= i) { self.frameCache.push(""); }
        got: str = self.frameCache.get(i);
        if (got.len > 0) { return got; }
        made: str = self.frameSlow(off);
        self.frameCache.set(i, made);
        return made;
    }

    frameSlow &self off:long -> str {
        s: String;
        s.pushStr("[rbp - ");
        s.pushLong(off);
        s.push(']');
        out: str = "";
        out = keepString(s);
        return out;
    }

    // Where a result is computed: the temp's own register, or the scratch when it has none.
    workReg &self t:Temp -> long {
        r: long = self.ra.regOf(t);
        if (r == SPILLED) { return SCRATCH; }
        return r;
    }

    // Write a result back to a spilled temp's slot. A temp that got a register was computed
    // there and needs nothing, which is what makes `workReg` + `store` one pattern rather than a
    // branch at every site.
    store &self t:Temp size:long -> void {
        if (self.ra.regOf(t) != SPILLED) { return; }
        self.put("mov ");
        self.put(self.place(t));
        self.put(", ");
        self.putLine(regNameSized(SCRATCH, size));
    }

    // Re-extend `r` into the canonical form of `k`. Nothing to do for a full word; a narrower
    // type has to say what its top bits mean, which is the difference between `int` arithmetic
    // wrapping at thirty-two bits and not wrapping at all, and between `(-56) as u8` being 200
    // and being -56.
    canonicalize &self r:long k:Lit -> void {
        w: long = widthOf(k);
        if (w >= 8) { return; }
        if (typeInfo(k).unsignedNum) {
            // Writing a 32-bit register clears the upper half on its own.
            if (w == 4) {
                self.put("mov ");
                self.put(regNameSized(r, 4));
                self.put(", ");
                self.putLine(regNameSized(r, 4));
                return;
            }
            self.put("movzx ");
        } else {
            if (w == 4) {
                if (r == REG_RAX) { self.putLine("cdqe"); return; }
                self.put("movsxd ");
                self.put(regName64(r));
                self.put(", ");
                self.putLine(regNameSized(r, 4));
                return;
            }
            self.put("movsx ");
        }
        self.put(regName64(r));
        self.put(", ");
        self.putLine(regNameSized(r, w));
    }

    // The address a PtrLoad or PtrStore reads, as the text inside its brackets: the base (in rax if
    // it has no register), and the scaled index when the access has one (in rdx if it has none).
    // When rdx is wanted for something else (`busy`) the sum is formed in rax with one `lea`.
    //
    // A base the allocator left to be computed again (`RegAlloc.markArgOnly`) joins the addressing
    // mode when it is a frame slot's address (`rbp`, its slot's distance below it going into
    // `addrDisp`) or, with no index, a global's (`rel`). The access then reads at `in.imm +
    // addrDisp`.
    address &self in:Instr busy:bool -> str {
        self.addrDisp = 0;
        base: str = "";
        rb: str = "";
        if (self.isRemat(in.a)) { rb = self.rematBase.get(in.a - self.spillBase); }
        if (rb.len > 0 && (in.x == NO_TEMP || rb == "rbp")) {
            base = rb;
            self.addrDisp = 0 - self.rematOff.get(in.a - self.spillBase);
        } else {
            base = self.intoScratch(in.a, SCRATCH);
        }
        if (in.x == NO_TEMP) { return base; }
        xr: long = self.ra.regOf(in.x);
        if (xr == SPILLED) { xr = self.intoScratchReg(in.x, SCRATCH2); }
        self.addrText.clear();
        self.addrText.pushStr(base);
        self.addrText.pushStr(" + ");
        self.addrText.pushStr(regName64(xr));
        if (in.scale > 1) { self.addrText.push('*'); self.addrText.pushLong(in.scale); }
        if (xr == SCRATCH2 && busy) {
            self.put("lea rax, [");
            unsafe { self.put(self.addrText.view()); }
            if (self.addrDisp < 0) { self.put(" - "); self.putNum(0 - self.addrDisp); }
            self.putLine("]");
            self.addrDisp = 0;
            return "rax";
        }
        v: str = "";
        unsafe { v = self.addrText.view(); }
        return v;
    }

    // Load a temp into a scratch register when it is spilled, so an instruction never has two
    // memory operands.
    intoScratch &self t:Temp which:long -> str {
        return regName64(self.intoScratchReg(t, which));
    }

    // Operand `b`, which `Opt::selectImmediates` may have turned into a literal riding on the
    // instruction. x86-64 encodes a 32-bit signed immediate on the arithmetic and compare forms,
    // which is the range the optimizer holds itself to.
    rightOperand &self in:Instr which:long -> str {
        if (!in.bIsImm) { return self.intoScratch(in.b, which); }
        return self.numText(in.bImm);
    }

    // Whether operand `b` of an integer comparison or `+ - * & | ^` may be read where it lies in
    // the frame (`cmp rbx, [rbp - 64]`) instead of through rdx. A temp the allocator left in the
    // frame has a slot of its own that every write of it stores to and nothing else writes, so
    // the slot holds its value wherever it is read. Not one computed again where it is read (no
    // slot), one with a register and a home (the home may be behind), or a float.
    rightInPlace &self in:Instr -> bool {
        return !gFrameOperandOff && !in.bIsImm && in.b != NO_TEMP && !isFloat(in.kind)
            && self.ra.regOf(in.b) == SPILLED && !self.isRemat(in.b);
    }

    // A small immediate as text, built once and kept. This compiler's own output has some
    // twenty-four thousand immediate operands, almost all between -128 and 1024, and calling
    // `format` and interning the result for every one of them is wasted work.
    numText &self v:long -> str {
        if (v < NUM_CACHE_LO || v > NUM_CACHE_HI) {
            out: str = "";
            out = keepString(format("{}", v));
            return out;
        }
        i: long = v - NUM_CACHE_LO;
        while (self.numCache.len() <= i) { self.numCache.push(""); }
        got: str = self.numCache.get(i);
        if (got.len > 0) { return got; }
        made: str = "";
        made = keepString(format("{}", v));
        self.numCache.set(i, made);
        return made;
    }

    // The same, as a register index. A byte or word operand has to be spelled as a sub-register
    // of the one the value is actually in, which the 64-bit name no longer says.
    intoScratchReg &self t:Temp which:long -> long {
        r: long = self.ra.regOf(t);
        if (r != SPILLED) { return r; }
        if (self.isRemat(t)) { self.materialize(t, which); return which; }
        self.put("mov ");
        self.put(regName64(which));
        self.put(", ");
        self.putLine(self.place(t));
        return which;
    }

    // ─── one instruction ─────────────────────────────────────────────────────

    emitInstr &self p:IRProgram fn:IRFunc in:Instr -> void {
        self.emitInstrOnly(p, fn, in);
        // A homed temp's home is written wherever the temp is, unless the writes are sunk to the
        // calls (`storeBefore`).
        if (gSinkHomesOff && in.dst != NO_TEMP && in.op != IROp.Nop && self.ra.isHomed(in.dst)) { self.homeMove(in.dst, true); }
    }

    // A homed temp (`RegAlloc.homed`) between its register and its home: written there, or read
    // back.
    homeMove &self t:Temp toHome:bool -> void {
        r: str = regName64(self.ra.regOf(t));
        h: str = self.frameText(self.spillAt.get(t - self.spillBase));
        self.put("mov ");
        if (toHome) { self.put(h); self.put(", "); self.putLine(r); }
        else { self.put(r); self.put(", "); self.putLine(h); }
    }

    // Before instruction `i`, a call, an `asm` block or a `memcpy`: each homed temp live across it
    // that may have changed since its home last held it, written there.
    storeBefore &self i:long -> void {
        if (gSinkHomesOff) { return; }
        f: long = self.ra.crossAt(i);
        if (f < 0) { return; }
        for k in f..f + self.ra.crossN(i) {
            t: Temp = self.ra.crossTemp(k);
            if (self.ra.isHomed(t) && self.ra.crossStored(k)) { self.homeMove(t, true); }
        }
    }

    // After instruction `i`, a call, an `asm` block or a `memcpy`: each homed temp live across
    // it whose register it may change (`RegAlloc.siteAt`), back in its register.
    reloadAfter &self i:long -> void {
        f: long = self.ra.crossAt(i);
        if (f < 0) { return; }
        m: long = self.ra.siteAt(i);
        for k in f..f + self.ra.crossN(i) {
            t: Temp = self.ra.crossTemp(k);
            if (self.ra.isHomed(t) && (m & (1 << self.ra.regOf(t))) != 0) { self.homeMove(t, false); }
        }
    }

    emitInstrOnly &self p:IRProgram fn:IRFunc in:Instr -> void {
        // An instruction the optimizer deleted. It stays in the list so no function's run moves;
        // nothing is emitted for it.
        if (in.op == IROp.Nop) { return; }
        // A value computed only for the branch after it (`RegAlloc.markFused`): the comparison
        // that branch makes is written here instead, and the branch is the jump alone.
        if (in.dst != NO_TEMP && self.ra.isFused(in.dst)) { self.emitFusedCompare(p, fn, in); return; }
        // A temp computed again where it is read is not computed here.
        if (in.dst != NO_TEMP && (in.op == IROp.Const || in.op == IROp.AddrOf || in.op == IROp.AggSlot
            || in.op == IROp.StrLitVal) && self.isRemat(in.dst)) { return; }
        // A fused compare-and-branch: what `Jz` on a comparison means, without the `setcc`, the
        // widening and the second compare against zero that spelling it as a value costs.
        if (in.op == IROp.Jcc) {
            if (isFloat(in.kind)) { self.emitFloatJcc(in); return; }
            self.emitTest(in);
            self.jumpOn(in.cmpOp, in.kind, in.name);
            return;
        }
        if (in.op == IROp.Label) {
            self.put(nameOf(in.name));
            self.putLine(":");
            if (self.landing.len() > 0) { self.emitLanding(in.name); }
            return;
        }
        if (in.op == IROp.RecoverPush) { self.emitRecoverPush(in); return; }
        if (in.op == IROp.FaultEdge) { return; }
        if (in.op == IROp.Const) {
            // A float constant for an `xmm` register: its bits through rax.
            xc: long = self.xmmOf(in.dst);
            if (xc >= 0) {
                self.movImm(REG_RAX, in.imm);
                self.put("movq ");
                self.put(regName64(xc));
                self.putLine(", rax");
                return;
            }
            // A literal already is the canonical word, so there is nothing to extend, but it
            // goes through the scratch when the destination is a slot: `mov [rbp - n], imm` names
            // no operand size, and a memory destination takes only a 32-bit immediate anyway.
            self.movImm(self.workReg(in.dst), in.imm);
            self.store(in.dst, 8);
            return;
        }
        // A named scalar's storage is a whole word (`declaredBytes` never gives a scalar less)
        // and what it holds is canonical, so a load and a store are each one full-width move.
        if (in.op == IROp.Load) {
            xl: long = self.xmmOf(in.dst);
            if (xl >= 0) {
                self.put("movq ");
                self.put(regName64(xl));
                self.put(", ");
                self.putLine(self.placeOfName(in));
                return;
            }
            // A slot or global holds its value's canonical word when written by name, but a store
            // through its address writes a narrow value at its own width and leaves the bytes
            // above as they were: `x: int = -1`, then `x = 5` through an `inout` lend or a
            // closure, leaves 0xFFFFFFFF00000005. A signed one whose address is taken is read at
            // its width and extended (an unsigned one's bytes above stay zero either way).
            w: long = widthOf(in.kind);
            if (w < 8 && isInteger(in.kind) && !typeInfo(in.kind).unsignedNum
                && ((!in.isGlobal && self.addrTaken.has(in.name as long)) || (in.isGlobal && self.globalsLent.has(in.name as long)))) {
                if (w == 4) { self.put("movsxd "); } else { self.put("movsx "); }
                self.put(regName64(self.workReg(in.dst)));
                if (w == 4) { self.put(", dword "); } else if (w == 2) { self.put(", word "); } else { self.put(", byte "); }
                self.putLine(self.placeOfName(in));
                self.store(in.dst, 8);
                return;
            }
            self.put("mov ");
            self.put(regName64(self.workReg(in.dst)));
            self.put(", ");
            self.putLine(self.placeOfName(in));
            self.store(in.dst, 8);
            return;
        }
        if (in.op == IROp.Store) {
            xs: long = self.xmmOf(in.a);
            if (xs >= 0) {
                // The slot holds the canonical word, as it would from a general register.
                self.xmmToRax(xs, floatClass(p.kindOf(in.a), p.structOf(in.a)) == 2);
                self.put("mov ");
                self.put(self.placeOfName(in));
                self.putLine(", rax");
                return;
            }
            v: str = self.intoScratch(in.a, SCRATCH);
            self.put("mov ");
            self.put(self.placeOfName(in));
            self.put(", ");
            self.putLine(v);
            return;
        }
        if (in.op == IROp.Mov) {
            if (self.xmmOf(in.dst) >= 0 || self.xmmOf(in.a) >= 0) { self.moveFloat(p, in); return; }
            // A spilled source into a register destination is one load, not a load into the
            // scratch and a copy out of it.
            d: long = self.ra.regOf(in.dst);
            if (d != SPILLED && self.isRemat(in.a)) { self.materialize(in.a, d); return; }
            if (d != SPILLED && self.ra.regOf(in.a) == SPILLED && in.a != NO_TEMP) {
                self.put("mov ");
                self.put(regName64(d));
                self.put(", ");
                self.putLine(self.place(in.a));
                return;
            }
            v: str = self.intoScratch(in.a, SCRATCH);
            // The two may share a register (`RegAlloc.takeOperandReg`): nothing to move.
            if (d != SPILLED && d == self.ra.regOf(in.a)) { return; }
            self.put("mov ");
            self.put(self.place(in.dst));
            self.put(", ");
            self.putLine(v);
            return;
        }
        if (in.op == IROp.Ret) {
            xr: long = self.xmmOf(in.a);
            if (xr >= 0) { self.xmmToRax(xr, floatClass(in.kind, in.structName) == 2); }
            else {
                v: str = self.intoScratch(in.a, SCRATCH);
                if (!(v == "rax")) {
                    self.put("mov rax, ");
                    self.putLine(v);
                }
            }
            // A float result is in `xmm0`, as System V has it; `rax` holds the same bits.
            if (floatClass(in.kind, in.structName) > 0) { self.putLine("movq xmm0, rax"); }
            if (self.atLast) { return; }
            self.put("jmp .end");
            self.putLine(fnLabelOf(fn.name));
            return;
        }
        if (in.op == IROp.RetVoid) {
            if (self.atLast) { return; }
            self.put("jmp .end");
            self.putLine(fnLabelOf(fn.name));
            return;
        }
        if (in.op == IROp.Jmp) {
            self.put("jmp ");
            self.putLine(nameOf(in.name));
            return;
        }
        if (in.op == IROp.Jz) {
            if (self.ra.isFused(in.a)) { self.jumpOn(IROp.CmpEq, in.kind, in.name); return; }
            if (self.isRemat(in.a)) { self.materialize(in.a, SCRATCH); }
            self.put("cmp ");
            if (self.isRemat(in.a)) { self.put("rax"); }
            else if (self.ra.regOf(in.a) != SPILLED) { self.put(self.place(in.a)); }
            else {
                self.put("qword ");
                self.put(self.place(in.a));
            }
            self.putLine(", 0");
            self.put("je ");
            self.putLine(nameOf(in.name));
            return;
        }
        if (in.op == IROp.AddrOf) {
            self.leaInto(in.dst, self.placeOfName(in));
            return;
        }
        if (in.op == IROp.PtrLoad) {
            // Straight into the destination's register when it has one: the load reads its base
            // before it writes, so the two may even be the same register.
            base: str = self.address(in, false);
            off: long = in.imm + self.addrDisp;
            xp: long = self.xmmOf(in.dst);
            if (xp >= 0) {
                if (in.kind == Lit.Float) { self.put("movss "); } else { self.put("movsd "); }
                self.put(regName64(xp));
                self.put(", ");
                self.putMem(base, off, widthOf(in.kind)); self.putLine("");
                return;
            }
            d: long = self.ra.regOf(in.dst);
            if (d != SPILLED) { self.emitSizedLoad(base, off, in.kind, d); return; }
            self.emitSizedLoad(base, off, in.kind, SCRATCH2);
            self.put("mov ");
            self.put(self.place(in.dst));
            self.putLine(", rdx");
            return;
        }
        if (in.op == IROp.PtrStore) {
            xv: long = self.xmmOf(in.b);
            w: long = widthOf(in.kind);
            // A constant value the store carries as its immediate (`RegAlloc.storesImmediate`):
            // the low `w` bytes, written as a signed number of that width.
            imm: bool = !in.bIsImm && self.isRemat(in.b) && self.ra.rematOf(in.b) == REMAT_CONST
                        && !isFloat(in.kind) && !isAggregate(in.kind);
            v: long = 0;
            if (imm) {
                v = self.rematVal.get(in.b - self.spillBase);
                if (w < 8) { v = (v << (64 - 8 * w)) >> (64 - 8 * w); }
                else if (v < 0 - 2147483648 || v > 2147483647) { imm = false; }
            }
            // The value needs rdx when it is in no register of its own, and so may a spilled index.
            base: str = self.address(in, !imm && (in.bIsImm || (xv < 0 && self.ra.regOf(in.b) == SPILLED)));
            off: long = in.imm + self.addrDisp;
            if (imm) {
                self.put("mov ");
                self.putMem(base, off, w);
                self.put(", ");
                self.putNum(v);
                self.putLine("");
                return;
            }
            if (xv >= 0 && !in.bIsImm) {
                if (in.kind == Lit.Float) { self.put("movss "); } else { self.put("movsd "); }
                self.putMem(base, off, w);
                self.put(", ");
                self.putLine(regName64(xv));
                return;
            }
            vr: long = self.intoScratchReg(in.b, SCRATCH2);
            self.put("mov ");
            self.putMem(base, off, w);
            self.put(", ");
            self.putLine(regNameSized(vr, w));
            return;
        }
        if (in.op == IROp.StrLitVal) {
            self.leaInto(in.dst, self.relOperand(strConstLabel(in.imm)));
            return;
        }
        // The literal's bytes themselves: what its pair's `ptr` word holds (`flow.k` folds a read
        // of that word to this).
        if (in.op == IROp.StrAddr) {
            self.leaInto(in.dst, self.relOperand(strBytesLabel(in.imm)));
            return;
        }
        if (in.op == IROp.AggSlot) {
            self.leaInto(in.dst, self.frameText(self.aggAt.get(in.imm)));
            return;
        }
        if (in.op == IROp.AggCopy) {
            self.emitBlockCopy(in);
            return;
        }
        if (in.op == IROp.AggZero) {
            self.emitBlockZero(in);
            return;
        }
        if (in.op == IROp.Asm) { self.emitAsmBlock(p, fn, in); return; }
        if (in.op == IROp.Atomic) { self.emitAtomic(p, in); return; }
        if (in.op == IROp.MemCopy) { self.emitMemCopy(p, fn, in); return; }
        if (in.op == IROp.Lea) { self.emitLea(in); return; }
        if (in.op == IROp.Call) { self.emitCall(p, in); return; }
        if (in.op == IROp.CallIndirect) { self.emitCallIndirect(p, in); return; }
        if (in.op == IROp.FnAddr) {
            self.leaInto(in.dst, self.relOperand(fnLabelOf(in.name)));
            return;
        }
        if (in.op == IROp.VtableAddr) {
            self.leaInto(in.dst, self.relOperand(nameOf(in.name)));
            return;
        }
        if (in.op == IROp.BNot) {
            v: str = self.intoScratch(in.a, SCRATCH);
            // In the destination's own register where it has one.
            bd: long = self.ra.regOf(in.dst);
            if (!gSetInPlaceOff && bd != SPILLED && !isXmm(bd)) {
                if (!(v == regName64(bd))) {
                    self.put("mov ");
                    self.put(regName64(bd));
                    self.put(", ");
                    self.putLine(v);
                }
                self.put("not ");
                self.putLine(regName64(bd));
                self.canonicalize(bd, in.kind);
                return;
            }
            self.put("mov rax, ");
            self.putLine(v);
            self.putLine("not rax");
            self.canonicalize(SCRATCH, in.kind);
            self.put("mov ");
            self.put(self.place(in.dst));
            self.putLine(", rax");
            return;
        }
        if (in.op == IROp.Bounds) { self.emitBounds(in); return; }
        if (in.op == IROp.Convert) { self.emitConvert(in); return; }
        if (isCompare(in.op)) { self.emitCompare(in); return; }
        self.emitArith(in);
    }

    // A load of exactly the pointee's width, extended into the full register. Reading eight bytes
    // for every load would make `f[i]` on a `[u8]` answer with eight characters at once (so a
    // format string's first `{` is never found), just as writing eight would make a one-byte
    // store trample the seven bytes after it.
    emitSizedLoad &self base:str off:long k:Lit r:long -> void {
        w: long = widthOf(k);
        if (w >= 8) {
            self.put("mov ");
            self.put(regName64(r));
            self.put(", ");
            self.putMem(base, off, 8); self.putLine("");
            return;
        }
        if (w == 4) {
            // A 32-bit destination register zeroes the upper half on its own; a signed source
            // has to say so, or `-1 as long` reads as four billion.
            if (typeInfo(k).unsignedNum) {
                self.put("mov ");
                self.put(regNameSized(r, 4));
                self.put(", ");
                self.putMem(base, off, 4); self.putLine("");
            } else {
                self.put("movsxd ");
                self.put(regName64(r));
                self.put(", ");
                self.putMem(base, off, 4); self.putLine("");
            }
            return;
        }
        if (typeInfo(k).unsignedNum) { self.put("movzx "); }
        else                         { self.put("movsx "); }
        self.put(regName64(r));
        self.put(", ");
        self.putMem(base, off, w); self.putLine("");
    }

    // The comparison a fused value stands for (`RegAlloc.markFused`), written where the value
    // would have been computed, every operand read where it is at that point. The branch it
    // feeds (whose operands these are) is written as its jump alone (`jumpOn`).
    emitFusedCompare &self p:IRProgram fn:IRFunc in:Instr -> void {
        br: Instr = p.code.get(fn.firstInstr + self.ra.fusedBranch(in.dst));
        if (in.op == IROp.Div || in.op == IROp.Mod) {
            // The result tested where the division leaves it, rax or rdx (it has no register,
            // so the division computes in its scratch), against the branch's other operand: an
            // immediate, or a temp in a register or a slot. One the emitter computes again goes
            // in the other scratch register.
            self.keepDiv = true;
            self.emitDivide(in);
            self.keepDiv = false;
            res: str = regName64(self.divRes);
            if (br.op == IROp.Jz || (br.bIsImm && br.bImm == 0)) {
                self.put("test ");
                self.put(res);
                self.put(", ");
                self.putLine(res);
                return;
            }
            rhs: str = "";
            if (br.bIsImm) { rhs = self.numText(br.bImm); }
            else if (self.isRemat(br.b)) {
                other: long = SCRATCH;
                if (self.divRes == SCRATCH) { other = SCRATCH2; }
                self.materialize(br.b, other);
                rhs = regName64(other);
            } else { rhs = self.place(br.b); }
            self.put("cmp ");
            self.put(res);
            self.put(", ");
            self.putLine(rhs);
            return;
        }
        if (in.op == IROp.BAnd) {
            // `a & b` against zero: `test a, b`.
            l: str = self.intoScratch(in.a, SCRATCH);
            r: str = self.rightOperand(in, SCRATCH2);
            self.put("test ");
            self.put(l);
            self.put(", ");
            self.putLine(r);
            return;
        }
        // A load compared with the branch's other operand (zero for a `Jz`) at the load's width:
        // `cmp dword [p], 0`, `cmp qword [p + rcx*8], rsi`. An operand in no register goes to rdx,
        // so the address keeps out of it.
        w: long = widthOf(in.kind);
        temp: bool = br.op == IROp.Jcc && !br.bIsImm;
        base: str = self.address(in, temp && self.ra.regOf(br.b) == SPILLED);
        off: long = in.imm + self.addrDisp;
        if (!temp) {
            v: long = 0;
            if (br.op == IROp.Jcc) { v = br.bImm; }
            self.put("cmp ");
            self.putMem(base, off, w);
            self.put(", ");
            self.putNum(v);
            self.putLine("");
            return;
        }
        rb: long = self.intoScratchReg(br.b, SCRATCH2);
        self.put("cmp ");
        self.putMem(base, off, w);
        self.put(", ");
        self.putLine(regNameSized(rb, w));
    }

    // The comparison an integer branch makes: nothing when it was written with the value it reads
    // (`RegAlloc.markFused`), and against zero `test r, r`, which sets the flags `cmp r, 0` does
    // (CF and OF clear, ZF and SF from r) in fewer bytes.
    emitTest &self in:Instr -> void {
        if (self.ra.isFused(in.a)) { return; }
        l: str = self.intoScratch(in.a, SCRATCH);
        if (in.bIsImm && in.bImm == 0) {
            self.put("test ");
            self.put(l);
            self.put(", ");
            self.putLine(l);
            return;
        }
        r: str = "";
        if (self.rightInPlace(in)) { r = self.place(in.b); } else { r = self.rightOperand(in, SCRATCH2); }
        self.put("cmp ");
        self.put(l);
        self.put(", ");
        self.putLine(r);
    }

    // ─── branches as conditional moves ──────────────────────────────────────

    // A branch that only chooses which of a few values registers get is written without the
    // branch: the comparison, then conditional moves. Both ways are computed, and the choice
    // costs the comparison and a move, where a branch the predictor cannot learn (collatz's
    // `n % 2 == 0`) refills the pipeline about half the time. Two shapes (`selShape`):
    //
    //   triangle   if (c) goto L; arm; L:                  the arm runs when c does not hold
    //   diamond    if (c) goto L1; A; goto L2; L1: B; L2:   A when c does not hold, B when it does
    //
    // An arm is a few instructions of integer arithmetic that cannot fault and write only
    // registers (`selOp`), each operand in a register (a copy may read a constant or an address
    // the emitter computes again). Running an arm on the way that skipped it is harmless where
    // what it writes is dead on that way. A value an arm computes only for itself has its range
    // inside the arm, so its register holds nothing live on the other way: anything live there
    // is live across the arm too. Every other value an arm writes is written with `cmov` under
    // the arm's own condition, or (a diamond's `d`, which both arms end by writing) written in
    // place by one arm and then replaced by the other arm's value under that one's condition.
    //
    // After the comparison only instructions that leave the flags alone are written (`mov`,
    // `lea`, re-extending a narrow value: `selFlagFree`). An arm of one instruction that would
    // set them is computed into rax before the comparison instead (`early`), which must then
    // read nothing through rax itself.
    markSelects &self p:IRProgram fn:IRFunc from:long -> void {
        n: long = fn.instrCount;
        self.selAt.clear();
        self.selIn.clear();
        self.sels.clear();
        for i in 0..n { self.selAt.push(-1); self.selIn.push(false); }
        if (gSelectOff) { return; }
        refs: HashMap<long, long>;
        counted: bool = false;
        for j in from..n {
            o: IROp = p.code[fn.firstInstr + j].op;
            if (o != IROp.Jcc && o != IROp.Jz) { continue; }
            r: SelRegion = SelRegion { br: j, start: j, end: -1, a0: -1, a1: -1, b0: -1, b1: -1,
                                       early: -1, late: -1, direct: NO_TEMP, inc: false };
            if (!self.selShape(p, fn, &r, from)) { continue; }
            // A diamond's second arm must be entered from the branch alone.
            if (r.b0 >= 0) {
                if (!counted) { countLabelRefs(p, fn, &refs); counted = true; }
                ways: long = 0;
                c: Option<long> = refs.find(p.code[fn.firstInstr + j].name as long);
                match c { Some(k) { ways = k; } None { } }
                if (ways != 1) { continue; }
            }
            if (!self.selPlan(p, fn, &r)) { continue; }
            self.selAt.set(r.start, self.sels.len());
            for k in r.start..r.end + 1 { self.selIn.set(k, true); }
            self.sels.push(r);
        }
    }

    // The shape around the branch at `r.br`: where its comparison is written, and its arms.
    selShape &self p:IRProgram fn:IRFunc inout r:SelRegion from:long -> bool {
        n: long = fn.instrCount;
        j: long = r.br;
        br: Instr = p.code.get(fn.firstInstr + j);
        if (br.op == IROp.Jcc && (isFloat(br.kind) || self.coldRun(p, fn, j) >= 0)) { return false; }
        // A value fused with the branch (`RegAlloc.markFused`) writes the comparison where it is.
        if (self.ra.isFused(br.a)) {
            s: long = j - 1;
            while (s >= from && p.code[fn.firstInstr + s].op == IROp.Nop) { s = s - 1; }
            if (s < from || p.code[fn.firstInstr + s].dst != br.a) { return false; }
            r.start = s;
        }
        x: long = j + 1;
        while (x < n && selOp(p.code[fn.firstInstr + x].op)) { x = x + 1; }
        if (x >= n || selCount(p, fn, j + 1, x - 1) == 0) { return false; }
        stop: Instr = p.code.get(fn.firstInstr + x);
        r.a0 = j + 1;
        r.a1 = x - 1;
        if (stop.op == IROp.Label && stop.name == br.name) {
            r.end = x - 1;
            return selCount(p, fn, r.a0, r.a1) <= MAX_SEL_ARM;
        }
        if (stop.op != IROp.Jmp) { return false; }
        l1: long = x + 1;
        while (l1 < n && p.code[fn.firstInstr + l1].op == IROp.Nop) { l1 = l1 + 1; }
        if (l1 >= n || p.code[fn.firstInstr + l1].op != IROp.Label || p.code[fn.firstInstr + l1].name != br.name) { return false; }
        y: long = l1 + 1;
        while (y < n && selOp(p.code[fn.firstInstr + y].op)) { y = y + 1; }
        if (y >= n || p.code[fn.firstInstr + y].op != IROp.Label || p.code[fn.firstInstr + y].name != stop.name) { return false; }
        r.b0 = l1 + 1;
        r.b1 = y - 1;
        r.end = y - 1;
        na: long = selCount(p, fn, r.a0, r.a1);
        nb: long = selCount(p, fn, r.b0, r.b1);
        return nb > 0 && na <= MAX_SEL_ARM && nb <= MAX_SEL_ARM && na + nb <= MAX_SEL_BOTH;
    }

    // How each arm is written, or false when one of them cannot be.
    selPlan &self p:IRProgram fn:IRFunc inout r:SelRegion -> bool {
        for k in r.a0..r.end + 1 {
            in: Instr = p.code.get(fn.firstInstr + k);
            if (in.op == IROp.Nop || in.op == IROp.Label || in.op == IROp.Jmp) { continue; }
            if (!self.selOperands(in)) { return false; }
        }
        if (r.b0 < 0) {
            // A triangle: every value the arm leaves behind keeps its old one on the way that
            // skipped it, so it must be in its register from before the branch.
            only: long = selOnly(p, fn, r.a0, r.a1);
            for k in r.a0..r.a1 + 1 {
                in: Instr = p.code.get(fn.firstInstr + k);
                if (in.op == IROp.Nop) { continue; }
                own: bool = self.ra.rangeWithin(in.dst, r.a0, r.a1);
                if (!own && !self.ra.liveBefore(in.dst, r.br)) { return false; }
                if (!selFlagFree(in)) {
                    if (own || k != only) { return false; }
                    r.early = k;
                }
            }
            if (only >= 0) {
                in: Instr = p.code.get(fn.firstInstr + only);
                r.inc = (in.op == IROp.Add || in.op == IROp.Sub) && in.a == in.dst && in.bIsImm && in.bImm == 1
                        && !self.ra.rangeWithin(in.dst, r.a0, r.a1);
                if (r.inc) { r.early = -1; }
            }
            return r.early < 0 || self.selCompareSparesRax(p, fn, r);
        }
        // A diamond: both arms end by writing one value, and write nothing else that lives on.
        la: long = selLast(p, fn, r.a0, r.a1);
        lb: long = selLast(p, fn, r.b0, r.b1);
        d: Temp = p.code[fn.firstInstr + la].dst;
        if (p.code[fn.firstInstr + lb].dst != d || self.ra.rangeWithin(d, r.a0, r.b1)) { return false; }
        if (!self.selLocals(p, fn, r.a0, la, r.a0, r.a1) || !self.selLocals(p, fn, r.b0, lb, r.b0, r.b1)) { return false; }
        freeA: bool = selAllFlagFree(p, fn, r.a0, r.a1);
        freeB: bool = selAllFlagFree(p, fn, r.b0, r.b1);
        oa: long = selOnly(p, fn, r.a0, r.a1);
        ob: long = selOnly(p, fn, r.b0, r.b1);
        // One arm written in place after the comparison, the other's value in rax or read from
        // the register it copies. The arms are written in their own order, A then B, so that
        // what one leaves in a register is never what the other has still to read; the one
        // exception is an arm of one instruction, which writes only rax (or nothing).
        if (freeB) {
            r.late = 1;
            if (oa >= 0 && !freeA) { r.early = oa; }
            else if (!freeA) { return false; }
            else if (oa >= 0) { r.direct = self.selCopySource(p, fn, oa, r.b0, r.b1); }
        } else if (freeA && ob >= 0) {
            r.late = 0;
            if (!selFlagFree(p.code.get(fn.firstInstr + ob))) { r.early = ob; }
            else { r.direct = self.selCopySource(p, fn, ob, r.a0, r.a1); }
        } else {
            return false;
        }
        return r.early < 0 || self.selCompareSparesRax(p, fn, r);
    }

    // Whether every instruction from `lo` to before `last` writes a value of its own, its range
    // inside the arm `a0..a1`.
    selLocals &self p:IRProgram fn:IRFunc lo:long last:long a0:long a1:long -> bool {
        for k in lo..last {
            in: Instr = p.code.get(fn.firstInstr + k);
            if (in.op == IROp.Nop) { continue; }
            if (!self.ra.rangeWithin(in.dst, a0, a1)) { return false; }
        }
        return true;
    }

    // When the one instruction at `k` is a copy out of a register the other arm (`lo..hi`) does
    // not write, the temp it copies: the `cmov` reads that register. Otherwise NO_TEMP.
    selCopySource &self p:IRProgram fn:IRFunc k:long lo:long hi:long -> Temp {
        in: Instr = p.code.get(fn.firstInstr + k);
        if (in.op != IROp.Mov || self.isRemat(in.a)) { return NO_TEMP; }
        src: long = self.ra.regOf(in.a);
        for m in lo..hi + 1 {
            w: Instr = p.code.get(fn.firstInstr + m);
            if (w.op != IROp.Nop && self.ra.regOf(w.dst) == src) { return NO_TEMP; }
        }
        return in.a;
    }

    // Whether `selCompute` can write `in`: an integer into a general register of its own, each
    // operand in a register or an immediate (a copy's may be computed again where it is read).
    selOperands &self in:Instr -> bool {
        if (in.dst == NO_TEMP || isFloat(in.kind) || isAggregate(in.kind) || self.xmmOf(in.dst) >= 0) { return false; }
        if (!selReg(self.ra.regOf(in.dst)) || self.ra.isFused(in.dst) || self.ra.isHomed(in.dst)) { return false; }
        // An arm is written from its left operand into its result: not into its right one's register.
        if (!in.bIsImm && in.b != NO_TEMP && in.b != in.a && self.ra.regOf(in.b) == self.ra.regOf(in.dst)) { return false; }
        if (in.op == IROp.Const) { return true; }
        if (in.op == IROp.Mov) { return self.isRemat(in.a) || self.selInReg(in.a); }
        if (in.op == IROp.Lea) { return (in.a == NO_TEMP || self.selInReg(in.a)) && self.selInReg(in.x); }
        if (!self.selInReg(in.a)) { return false; }
        if (in.bIsImm) { return in.bImm != 0 - 2147483648; }
        if (in.op == IROp.Shl || in.op == IROp.Shr) { return false; }
        return self.selInReg(in.b);
    }

    // `t` in a general register, not computed again where it is read.
    selInReg &self t:Temp -> bool {
        return t != NO_TEMP && !self.isRemat(t) && self.xmmOf(t) < 0 && selReg(self.ra.regOf(t));
    }

    // Whether the comparison the region writes leaves rax alone, which holds the early arm's
    // value by then: its operands in registers, and no division (whose result is formed there).
    // A right operand may be the value `rax` holds (`RegAlloc.spillScratch`), which the early arm
    // would destroy.
    selCompareSparesRax &self p:IRProgram fn:IRFunc r:SelRegion -> bool {
        br: Instr = p.code.get(fn.firstInstr + r.br);
        if (br.op == IROp.Jcc && !br.bIsImm && self.ra.regOf(br.b) == REG_RAX) { return false; }
        if (r.start == r.br) { return self.selInReg(br.a); }
        w: Instr = p.code.get(fn.firstInstr + r.start);
        if (w.op == IROp.BAnd) { return self.selInReg(w.a); }
        if (w.op != IROp.PtrLoad) { return false; }
        if (w.x != NO_TEMP && !self.selInReg(w.x)) { return false; }
        if (self.selInReg(w.a)) { return true; }
        // A frame slot's address, or with no index a global's, joins the addressing mode (`address`).
        if (!self.isRemat(w.a)) { return false; }
        rb: str = self.rematBase.get(w.a - self.spillBase);
        return rb.len > 0 && (w.x == NO_TEMP || rb == "rbp");
    }

    // The region written in place of the branch (`markSelects`).
    emitRegion &self p:IRProgram fn:IRFunc r:SelRegion -> void {
        br: Instr = p.code.get(fn.firstInstr + r.br);
        if (r.early >= 0) { self.selCompute(p.code.get(fn.firstInstr + r.early), REG_RAX); }
        if (r.start < r.br) { self.emitInstr(p, fn, p.code.get(fn.firstInstr + r.start)); }
        jc: Instr = br;
        if (br.op == IROp.Jz) {
            jc = instr(IROp.Jcc);
            jc.a = br.a;
            jc.bIsImm = true;
            jc.bImm = 0;
            jc.kind = p.kindOf(br.a);
            jc.cmpOp = IROp.CmpEq;
        }
        self.emitTest(jc);
        unsigned: bool = typeInfo(jc.kind).unsignedNum;
        taken: str = setSuffix(jc.cmpOp, unsigned);
        skipped: str = setSuffix(negateCompare(jc.cmpOp), unsigned);
        if (r.b0 < 0) {
            if (r.inc) {
                // `d = d + 1` where the arm ran: the flag, added.
                in: Instr = p.code.get(fn.firstInstr + selOnly(p, fn, r.a0, r.a1));
                d: long = self.ra.regOf(in.dst);
                self.put("set");
                self.put(skipped);
                self.putLine(" al");
                self.putLine("movzx eax, al");
                if (in.op == IROp.Add) { self.put("add "); } else { self.put("sub "); }
                self.put(regName64(d));
                self.putLine(", rax");
                self.canonicalize(d, in.kind);
                return;
            }
            for k in r.a0..r.a1 + 1 {
                in: Instr = p.code.get(fn.firstInstr + k);
                if (in.op == IROp.Nop) { continue; }
                if (self.ra.rangeWithin(in.dst, r.a0, r.a1)) { self.selCompute(in, self.ra.regOf(in.dst)); continue; }
                if (k == r.early) { self.selMove(skipped, in.dst, REG_RAX); continue; }
                if (in.op == IROp.Mov && !self.isRemat(in.a)) { self.selMove(skipped, in.dst, self.ra.regOf(in.a)); continue; }
                self.selCompute(in, REG_RAX);
                self.selMove(skipped, in.dst, REG_RAX);
            }
            return;
        }
        // A diamond: one arm in place, then the other's value moved in under its condition.
        d: Temp = p.code[fn.firstInstr + selLast(p, fn, r.a0, r.a1)].dst;
        cc: str = taken;
        lo: long = r.a0; hi: long = r.a1;       // the arm whose value comes in by `cmov`
        wl: long = r.b0; wh: long = r.b1;       // the arm written in place
        if (r.late == 0) { lo = r.b0; hi = r.b1; wl = r.a0; wh = r.a1; }
        else { cc = skipped; }
        if (r.early < 0 && r.direct == NO_TEMP) {
            for k in lo..hi + 1 {
                in: Instr = p.code.get(fn.firstInstr + k);
                if (in.op == IROp.Nop) { continue; }
                if (in.dst == d) { self.selCompute(in, REG_RAX); } else { self.selCompute(in, self.ra.regOf(in.dst)); }
            }
        }
        for k in wl..wh + 1 {
            in: Instr = p.code.get(fn.firstInstr + k);
            if (in.op != IROp.Nop) { self.selCompute(in, self.ra.regOf(in.dst)); }
        }
        if (r.direct != NO_TEMP) { self.selMove(cc, d, self.ra.regOf(r.direct)); }
        else { self.selMove(cc, d, REG_RAX); }
    }

    // `cmov<cc> d, src`.
    selMove &self cc:str d:Temp src:long -> void {
        self.put("cmov");
        self.put(cc);
        self.put(" ");
        self.put(regName64(self.ra.regOf(d)));
        self.put(", ");
        self.putLine(regName64(src));
    }

    // `in`'s value into register `r`, its operands read where they are (`selOperands`). What
    // `selFlagFree` accepts is written without touching the flags; anything else only into rax,
    // before the comparison, where `r` is no operand's register.
    selCompute &self in:Instr r:long -> void {
        rn: str = regName64(r);
        o: IROp = in.op;
        // A constant or a copy is already the canonical word of its type.
        if (o == IROp.Const) {
            self.movImm(r, in.imm);
            return;
        }
        if (o == IROp.Mov) {
            if (self.isRemat(in.a)) { self.materialize(in.a, r); }
            else if (self.ra.regOf(in.a) != r) {
                self.put("mov ");
                self.put(rn);
                self.put(", ");
                self.putLine(regName64(self.ra.regOf(in.a)));
            }
            return;
        }
        if (o == IROp.Lea) {
            base: str = "";
            if (in.a != NO_TEMP) { base = regName64(self.ra.regOf(in.a)); }
            self.put("lea ");
            self.put(rn);
            self.put(", [");
            self.putLeaSum(base, regName64(self.ra.regOf(in.x)), in.scale, in.imm);
            self.putLine("]");
            return;
        }
        if (selFlagFree(in)) {
            a: str = regName64(self.ra.regOf(in.a));
            self.put("lea ");
            self.put(rn);
            self.put(", [");
            if (o == IROp.Mul) {
                self.put(a);
                self.put(" + ");
                self.put(a);
                self.put("*");
                self.putNum(in.bImm - 1);
            } else if (o == IROp.Shl) {
                if (in.bImm == 1) { self.put(a); self.put(" + "); self.put(a); }
                else { self.put(a); self.put("*"); self.putNum(1 << in.bImm); }
            } else if (!in.bIsImm) {
                self.put(a);
                self.put(" + ");
                self.put(regName64(self.ra.regOf(in.b)));
            } else {
                v: long = in.bImm;
                if (o == IROp.Sub) { v = 0 - v; }
                self.put(a);
                if (v < 0) { self.put(" - "); self.putNum(0 - v); } else { self.put(" + "); self.putNum(v); }
            }
            self.putLine("]");
        } else if (o == IROp.Mul && in.bIsImm) {
            self.put("imul ");
            self.put(rn);
            self.put(", ");
            self.put(regName64(self.ra.regOf(in.a)));
            self.put(", ");
            self.putNum(in.bImm);
            self.putLine("");
        } else {
            self.put("mov ");
            self.put(rn);
            self.put(", ");
            self.putLine(regName64(self.ra.regOf(in.a)));
            mn: str = mnemonic(o);
            if (o == IROp.Shr && typeInfo(in.kind).unsignedNum) { mn = "shr"; }
            self.put(mn);
            self.put(" ");
            self.put(rn);
            self.put(", ");
            if (in.bIsImm && (o == IROp.Shl || o == IROp.Shr)) { self.putNum(in.bImm % 64); }
            else if (in.bIsImm) { self.putNum(in.bImm); }
            else { self.put(regName64(self.ra.regOf(in.b))); }
            self.putLine("");
        }
        self.canonicalize(r, in.kind);
    }

    // `j<cc> label` on the flags already set: a branch whose comparison was written with the value
    // it reads (`emitFusedCompare`).
    jumpOn &self op:IROp k:Lit name:Sym -> void {
        self.put("j");
        self.put(setSuffix(op, typeInfo(k).unsignedNum));
        self.put(" ");
        self.putLine(nameOf(name));
    }

    // Unless (unsigned) index < length, say what happened and abort. The in-range path is one
    // compare and one branch not taken; the report is all on the cold side, past the function's
    // `ret`. The compare is unsigned, so a negative index looks enormous and fails the same test.
    //
    // A slice check (`imm` is one of the `BOUNDS_SLICE_*` kinds) is inclusive (`end <= len`,
    // `start <= end`), and each kind has its own report, because an end past the length and a
    // range written backwards are different mistakes.
    emitBounds &self in:Instr -> void {
        range: bool = in.imm != BOUNDS_INDEX;
        n: long = self.boundsN;
        self.boundsN = n + 1;
        self.needBounds = true;
        if (range) { self.needSlice = self.needSlice | (1 << in.imm); }

        // The index is compared in its own register, or in rax when it has none.
        idx: str = self.intoScratch(in.a, SCRATCH);
        // A length computed again goes through rdx, which the cold side then reads it from; a
        // constant that fits is the compare's immediate, and the cold side's.
        lenAt: str = "rdx";
        if (self.isRemat(in.b) && self.ra.rematOf(in.b) == REMAT_CONST
            && self.rematVal.get(in.b - self.spillBase) >= 0 - 2147483648 && self.rematVal.get(in.b - self.spillBase) <= 2147483647) {
            lenAt = self.numText(self.rematVal.get(in.b - self.spillBase));
        } else if (self.isRemat(in.b)) { self.materialize(in.b, SCRATCH2); } else { lenAt = self.place(in.b); }
        self.put("cmp ");
        self.put(idx);
        self.put(", ");
        self.putLine(lenAt);
        if (range) { self.put("ja "); } else { self.put("jae "); }
        self.put(".boundsfail");
        self.putNum(n);
        self.putLine("");

        // The report, out of line, where nothing has changed since the compare. The index goes
        // to rax first, which no value lives in; then the length to rsi and the index to rdi, so
        // neither is overwritten while the other still needs it.
        self.coldAside.push(self.cold.length());
        self.coldLine(".boundsfail", n, ":");
        if (!(idx == "rax")) {
            self.cold.pushStr("mov rax, ");
            self.cold.pushStr(idx);
            self.coldNl();
        }
        if (!(lenAt == "rsi")) {
            self.cold.pushStr("mov rsi, ");
            self.cold.pushStr(lenAt);
            self.coldNl();
        }
        self.cold.pushStr("mov rdi, rax");
        self.coldNl();
        // rdx:rcx is where the index was written, the {bytes, length} of a `file:line`. A zero
        // length means there is no location to give, and the report prints the numbers alone.
        if (in.name == NO_SYM) {
            self.cold.pushStr("xor rdx, rdx");
            self.coldNl();
            self.cold.pushStr("xor rcx, rcx");
            self.coldNl();
        } else {
            text: str = nameOf(in.name);
            self.cold.pushStr("lea rdx, [rel ");
            self.cold.pushStr(locLabel(self.locIndex(in.name)));
            self.cold.pushStr("]");
            self.coldNl();
            self.cold.pushStr("mov ecx, ");      // a length: the 32-bit form, five bytes
            self.cold.pushLong(text.len);
            self.coldNl();
        }
        self.cold.pushStr("call ");
        if (in.imm == BOUNDS_SLICE_END) { self.cold.pushStr("__methRangeFail"); }
        else if (in.imm == BOUNDS_SLICE_ORDER) { self.cold.pushStr("__methOrderFail"); }
        else if (in.imm == BOUNDS_SLICE_START) { self.cold.pushStr("__methStartFail"); }
        else { self.cold.pushStr("__methBoundsFail"); }
        self.coldNl();
        self.coldAside.push(self.cold.length());
    }

    // The label a location's bytes get, adding it on first sighting. Deduplicated, because one
    // line indexed in a loop is one check emitted once but every `[` in a file is its own entry.
    locIndex &self s:Sym -> long {
        hit: Option<long> = self.locIx.find(s as long);
        match hit { Some(i) { return i; } None { } }
        self.locIx.put(s as long, self.locs.len());
        self.locs.push(s);
        return self.locs.len() - 1;
    }
    coldLine &self a:str n:long b:str -> void {
        self.cold.pushStr(a);
        self.cold.pushLong(n);
        self.cold.pushStr(b);
        self.coldNl();
    }
    coldNl &self -> void { self.cold.push('\n'); }

    // `x as T` is exactly the canonical form of T, which is one instruction and not the
    // two-operand arithmetic the fallthrough would treat it as. It is the source's low bytes
    // re-extended by the target's signedness, so widening a signed source sign-extends and an
    // unsigned one zero-extends, narrowing keeps the low bytes and extends them again, and a
    // same-width change of signedness is a real instruction rather than nothing at all. That last
    // case is why `s as u32` stops being negative, and so why `(s as u32) >> 2` shifts in zeroes.
    emitConvert &self in:Instr -> void {
        if (!isFloat(in.fromKind) && !isFloat(in.toKind) && self.xmmOf(in.a) < 0) {
            self.emitIntConvert(in);
            return;
        }
        xa: long = self.xmmOf(in.a);
        if (xa >= 0) { self.xmmToRax(xa, in.fromKind == Lit.Float); }
        else {
            v: str = self.intoScratch(in.a, SCRATCH);
            if (!(v == "rax")) {
                self.put("mov rax, ");
                self.putLine(v);
            }
        }
        if (isFloat(in.fromKind) || isFloat(in.toKind)) {
            self.emitFloatConvert(in.fromKind, in.toKind);
            xd: long = self.xmmOf(in.dst);
            if (xd >= 0) { self.put("movq "); self.put(regName64(xd)); self.putLine(", rax"); return; }
            self.put("mov ");
            self.put(self.place(in.dst));
            self.putLine(", rax");
            return;
        }
        self.canonicalize(SCRATCH, in.toKind);
        self.put("mov ");
        self.put(self.place(in.dst));
        self.putLine(", rax");
    }

    // An integer conversion. A value is held in its type's canonical form (sign- or zero-extended
    // to 64 bits), so a widening from a type whose form is already the target's (`u8` to `int`,
    // `int` to `long`) and a change of signedness at 64 bits are a move or nothing. The rest
    // extend the source's low bytes straight into the destination: `movsxd rbx, ecx`,
    // `movzx ebx, byte [rbp - 8]`, `mov ebx, ecx` for a `u32`.
    emitIntConvert &self in:Instr -> void {
        w: long = widthOf(in.toKind);
        fw: long = widthOf(in.fromKind);
        toU: bool = typeInfo(in.toKind).unsignedNum;
        fromU: bool = typeInfo(in.fromKind).unsignedNum;
        same: bool = w >= 8 || (fw < w && (fromU || !toU)) || (fw == w && fromU == toU);
        d: long = self.ra.regOf(in.dst);
        if (same) {
            if (d != SPILLED && self.isRemat(in.a)) { self.materialize(in.a, d); return; }
            if (d != SPILLED && d == self.ra.regOf(in.a)) { return; }
            if (d != SPILLED && self.ra.regOf(in.a) == SPILLED) {
                self.put("mov ");
                self.put(regName64(d));
                self.put(", ");
                self.putLine(self.place(in.a));
                return;
            }
            v: str = self.intoScratch(in.a, SCRATCH);
            self.put("mov ");
            self.put(self.place(in.dst));
            self.put(", ");
            self.putLine(v);
            return;
        }
        r: long = d;
        if (r == SPILLED) { r = SCRATCH; }
        // The source: a register, or its slot read at the target's width.
        sr: long = -1;
        if (self.isRemat(in.a)) { self.materialize(in.a, SCRATCH); sr = SCRATCH; }
        else if (self.ra.regOf(in.a) != SPILLED) { sr = self.ra.regOf(in.a); }
        if (w == 4 && !toU && r == REG_RAX && sr == REG_RAX) { self.putLine("cdqe"); }
        else {
            if (w == 4 && toU) { self.put("mov "); self.put(regNameSized(r, 4)); }
            else if (w == 4)   { self.put("movsxd "); self.put(regName64(r)); }
            else if (toU)      { self.put("movzx "); self.put(regNameSized(r, 4)); }
            else               { self.put("movsx "); self.put(regName64(r)); }
            self.put(", ");
            if (sr >= 0) { self.putLine(regNameSized(sr, w)); }
            else {
                if (w == 1) { self.put("byte "); } else if (w == 2) { self.put("word "); } else { self.put("dword "); }
                self.putLine(self.place(in.a));
            }
        }
        if (d == SPILLED) {
            self.put("mov ");
            self.put(self.place(in.dst));
            self.putLine(", rax");
        }
    }

    // Arguments go to their registers, then the call, then the result comes out of rax.
    emitCall &self p:IRProgram in:Instr -> void {
        pushed: long = self.emitArgs(p, in, false);
        self.put("call ");
        self.putLine(fnLabelOf(in.name));
        self.dropStackArgs(pushed);
        self.callResult(p, in);
    }

    // A call's result into its destination: from `xmm0` for a float (straight into the
    // destination's own `xmm` register when it has one), from rax otherwise, where a result the
    // next instruction reads may simply stay (`RegAlloc.markRaxPairs`). A result nothing reads
    // goes nowhere.
    callResult &self p:IRProgram in:Instr -> void {
        if (in.dst == NO_TEMP || self.ra.regOf(in.dst) == REG_RAX || self.ra.unread(in.dst)) { return; }
        xd: long = self.xmmOf(in.dst);
        if (xd >= 0) {
            self.put("movaps ");
            self.put(regName64(xd));
            self.putLine(", xmm0");
            return;
        }
        if (floatClass(p.kindOf(in.dst), p.structOf(in.dst)) > 0) { self.putLine("movq rax, xmm0"); }
        self.put("mov ");
        self.put(self.place(in.dst));
        self.putLine(", rax");
    }

    // The same as a direct call, except the callee is a value. It is parked in a scratch slot
    // first: the argument registers are written next, and on this compiler's convention argument
    // `k` goes in register `k`, so a callee still sitting in one of those would be overwritten
    // before it could be called.
    emitCallIndirect &self p:IRProgram in:Instr -> void {
        pushed: long = self.emitArgs(p, in, true);
        self.put("call qword ");
        self.putLine(self.calleeSlot());
        self.dropStackArgs(pushed);
        self.callResult(p, in);
    }

    // Argument `k` is passed in register `k`, so writing them in order destroys any argument whose
    // value is still sitting in an earlier argument's register. In `g(a, b, c)` with `c` in rbx,
    // once rbx holds `b` the value of `c` is gone. That is the only hazard, and it can be checked:
    // a spilled source cannot be clobbered by a register write at all, and a source in a register
    // is only at risk when that register belongs to an earlier argument. When no source is at
    // risk, which is most calls, the values go straight to their registers; otherwise they all go
    // through staging slots first, where no register write can reach them.
    //
    // Returns how many bytes of stack arguments it pushed, for the caller to drop after the call.
    emitArgs &self p:IRProgram in:Instr indirect:bool -> long {
        // Where each argument goes: a float to the next of the first eight `xmm` registers, the
        // rest to the next of the first ten general ones, and past those to the stack, eight bytes
        // each in order (System V's rule for what the registers do not hold).
        stacked: long = 0;
        ints: long = 0;
        floats: long = 0;
        for k in 0..in.argCount {
            t: Temp = p.args.get(in.firstArg + k);
            if (floatClass(p.kindOf(t), p.structOf(t)) > 0) {
                if (floats < FLOAT_ARG_REGS) { floats = floats + 1; } else { stacked = stacked + 1; }
            } else if (ints < INT_ARG_REGS) { ints = ints + 1; }
            else { stacked = stacked + 1; }
        }
        // The callee address lands in memory before any argument register is written, so it can
        // never be one of the things clobbered.
        if (indirect) { self.moveToSlot(self.calleeSlot(), in.a); }
        // The stack arguments next, through the scratch, before any argument register is written:
        // the block is a multiple of sixteen, so `rsp` is still aligned at the call. Every frame
        // operand is `rbp`-relative, so moving `rsp` moves none of them. No value lives in the
        // scratch (`rax` and `rdx` are never allocated), so nothing is lost passing through it.
        bytes: long = alignUp16(8 * stacked);
        if (stacked > 0) {
            self.put("sub rsp, ");
            self.putNum(bytes);
            self.putLine("");
        }
        ints = 0;
        floats = 0;
        stacked = 0;
        for k in 0..in.argCount {
            t: Temp = p.args.get(in.firstArg + k);
            if (floatClass(p.kindOf(t), p.structOf(t)) > 0) {
                if (floats < FLOAT_ARG_REGS) { floats = floats + 1; continue; }
            } else if (ints < INT_ARG_REGS) { ints = ints + 1; continue; }
            self.moveToSlot(keepString(format("qword [rsp + {}]", 8 * stacked)), t);
            stacked = stacked + 1;
        }
        // The float registers: a float lives in a general register (as its bits), an allocated
        // `xmm` register from `xmm8` up, or the frame, never in `xmm0`-`xmm7`, so these writes
        // clobber nothing another argument reads. They go before the general registers are
        // written, which is what they may read.
        floats = 0;
        for k in 0..in.argCount {
            t: Temp = p.args.get(in.firstArg + k);
            if (floatClass(p.kindOf(t), p.structOf(t)) == 0 || floats >= FLOAT_ARG_REGS) { continue; }
            self.put("movq xmm");
            self.putNum(floats);
            self.put(", ");
            self.putLine(self.place(t));
            floats = floats + 1;
        }
        // The general registers, as one parallel move: argument `k` into register `k` from
        // wherever the allocator put its value. A move is made once nothing still to be moved
        // reads its destination. When every move left waits on another, the ones left form
        // cycles, and an `xchg` puts one value in place and hands its register's old value on to
        // whichever move reads it. A source in memory or computed again in place never blocks.
        self.pmDst.clear();
        self.pmSrc.clear();
        self.pmTemp.clear();
        ints = 0;
        for k in 0..in.argCount {
            t: Temp = p.args.get(in.firstArg + k);
            if (floatClass(p.kindOf(t), p.structOf(t)) > 0 || ints >= INT_ARG_REGS) { continue; }
            r: long = self.ra.regOf(t);
            if (r == SPILLED || r >= REG_COUNT) { r = -1; }
            if (r != ints) {
                self.pmDst.push(ints);
                self.pmSrc.push(r);
                self.pmTemp.push(t);
            }
            ints = ints + 1;
        }
        while (self.pmDst.len() > 0) {
            done: bool = false;
            m: long = 0;
            while (m < self.pmDst.len()) {
                d: long = self.pmDst.get(m);
                if (self.pmRead(d)) { m = m + 1; continue; }
                self.pmEmit(m);
                done = true;
            }
            if (done) { continue; }
            // Every move left reads another's destination: break a cycle at the first.
            d: long = self.pmDst.get(0);
            sr: long = self.pmSrc.get(0);
            self.put("xchg ");
            self.put(regName(d));
            self.put(", ");
            self.putLine(regName(sr));
            self.pmDrop(0);
            for j in 0..self.pmDst.len() {
                if (self.pmSrc.get(j) == d) { self.pmSrc.set(j, sr); }
                else if (self.pmSrc.get(j) == sr) { self.pmSrc.set(j, d); }
            }
            // A move the exchange completed (its value now in its own register) is done.
            m2: long = 0;
            while (m2 < self.pmDst.len()) {
                if (self.pmSrc.get(m2) == self.pmDst.get(m2)) { self.pmDrop(m2); } else { m2 = m2 + 1; }
            }
        }
        return bytes;
    }

    // Whether a move still to be made reads register `r`.
    pmRead &self r:long -> bool {
        for j in 0..self.pmSrc.len() { if (self.pmSrc.get(j) == r) { return true; } }
        return false;
    }

    // Make pending move `m` and take it off the list.
    pmEmit &self m:long -> void {
        d: long = self.pmDst.get(m);
        sr: long = self.pmSrc.get(m);
        t: Temp = self.pmTemp.get(m);
        self.pmDrop(m);
        if (sr >= 0) {
            self.put("mov ");
            self.put(regName(d));
            self.put(", ");
            self.putLine(regName(sr));
            return;
        }
        if (self.isRemat(t)) { self.materialize(t, d); return; }
        self.put("mov ");
        self.put(regName(d));
        self.put(", ");
        self.putLine(self.place(t));
    }

    pmDrop &self m:long -> void {
        last: long = self.pmDst.len() - 1;
        self.pmDst.set(m, self.pmDst.get(last));
        self.pmSrc.set(m, self.pmSrc.get(last));
        self.pmTemp.set(m, self.pmTemp.get(last));
        self.pmDst.pop();
        self.pmSrc.pop();
        self.pmTemp.pop();
    }

    // After a call that passed arguments on the stack: they are the caller's to drop.
    dropStackArgs &self bytes:long -> void {
        if (bytes == 0) { return; }
        self.put("add rsp, ");
        self.putNum(bytes);
        self.putLine("");
    }

    // A temp into an arbitrary memory operand, going through the scratch when the temp is itself
    // in a slot, since x86 has no memory-to-memory move.
    moveToSlot &self dst:str t:Temp -> void {
        if (self.xmmOf(t) >= 0) {
            self.put("movq ");
            self.put(dst);
            self.put(", ");
            self.putLine(regName64(self.xmmOf(t)));
            return;
        }
        src: str = self.intoScratch(t, SCRATCH);
        self.put("mov ");
        self.put(dst);
        self.put(", ");
        self.putLine(src);
    }

    // Where argument `k` is staged, as an operand.
    argSlot &self k:long -> str {
        s: String;
        s.pushStr("[rbp - ");
        s.pushLong(self.argAt.get(k));
        s.push(']');
        out: str = "";
        out = keepString(s);
        return out;
    }

    // Inputs into their registers, the literal lines verbatim, then outputs back to their
    // variables. The allocator already treated the whole block as a clobber, so nothing live is
    // sitting in a caller-saved register across it.
    emitAsmBlock &self p:IRProgram fn:IRFunc in:Instr -> void {
        self.emitAsmInputs(p, in);
        // The programmer's assembly, verbatim except for `{reg}` placeholders, which become the
        // sub-register as wide as the value an `in` bound to that register.
        for k in 0..in.pieceCount {
            at: long = in.firstPiece + k;
            if (p.asmKinds.get(at) == AsmKind.Text) {
                self.putRawLine(self.resolveAsmRegs(p, in, nameOf(p.asmText.get(at))));
            }
        }
        for k in 0..in.pieceCount {
            at: long = in.firstPiece + k;
            if (p.asmKinds.get(at) != AsmKind.Out) { continue; }
            reg: str = nameOf(p.asmRegs.get(at));
            // The block's one output, gone to a promoted local's temp (`Opt.promoteLocals`): a
            // move into wherever that temp is, `movq` where either side is an `xmm` register.
            if (p.asmNames.get(at) == NO_SYM) {
                to: str = self.place(in.dst);
                if (isXmm(self.ra.regOf(in.dst)) || strStartsWith(reg, "xmm")) { self.put("movq "); } else { self.put("mov "); }
                self.put(to);
                self.put(", ");
                self.putLine(reg);
                continue;
            }
            // Into the slot, a whole word: `movq` from an `xmm` register (`mov` takes none). A
            // slot holds its integer's canonical word, which the register need not: `lock xadd
            // [rbx], ax` leaves whatever was above `ax`. So for a local narrower than a word the
            // register is first extended from the local's width, as its type says.
            nk: Lit = slotKindIn(p, fn, p.asmNames.get(at));
            if (!strStartsWith(reg, "xmm") && widthOf(nk) < 8 && nk != Lit.Float && nk != Lit.Double && nk != Lit.Void) {
                self.canonicalize(regIndexOf(reg), nk);
            }
            if (strStartsWith(reg, "xmm")) { self.put("movq "); } else { self.put("mov "); }
            self.put(self.slotOf(p.asmNames.get(at)));
            self.put(", ");
            self.putLine(reg);
        }
    }

    // Each input into the register the block asked for. Not simply in the order written: a value
    // may be sitting in a register another input wants, and moving that one first destroys it.
    // `memcpy`'s `in rdi dst; in rsi src; in rcx n` with `n` in rdi is such a case: loading `dst`
    // into rdi before rcx reads `n` made every buffered write copy a pointer's worth of bytes. So
    // a move is made only once no pending move still reads its target, and a cycle of moves is
    // broken with `xchg` (see below).
    emitAsmInputs &self p:IRProgram in:Instr -> void {
        want: Vec<str>;      // the register each input names
        have: Vec<str>;      // where its value is now
        for k in 0..in.pieceCount {
            at: long = in.firstPiece + k;
            if (p.asmKinds.get(at) == AsmKind.In) {
                want.push(nameOf(p.asmRegs.get(at)));
                have.push(self.place(p.asmVals.get(at)));
            }
        }
        done: Vec<bool>;
        k: long = 0;
        while (k < want.len()) { done.push(false); k = k + 1; }

        left: long = want.len();
        while (left > 0) {
            moved: bool = false;
            k = 0;
            while (k < want.len()) {
                if (!done.get(k) && !self.readsLater(want, have, done, k)) {
                    // Already there (a value the allocator left in place, or one an `xchg` put
                    // there) needs no move.
                    if (want.get(k) != have.get(k)) {
                        self.put("mov ");
                        self.put(want.get(k));
                        self.put(", ");
                        self.putLine(have.get(k));
                    }
                    done.set(k, true);
                    left = left - 1;
                    moved = true;
                }
                k = k + 1;
            }
            if (moved) { continue; }
            // Every remaining move is blocked by another, so they form a cycle of registers. It
            // is closed with `xchg`: move `k` reads a register that another pending move targets,
            // and swapping the two puts k's value in place while the target's old value moves to
            // where k's was, so any pending move that read either register now reads the other.
            // No third register is borrowed: parking a value in the scratch (`rax`) would clobber
            // the block's own `in rax` if that had already been loaded.
            k = self.cycleMove(want, have, done);
            src: str = have.get(k);
            dst: str = want.get(k);
            self.put("xchg ");
            self.put(dst);
            self.put(", ");
            self.putLine(src);
            done.set(k, true);
            left = left - 1;
            for j in 0..want.len() {
                if (!done.get(j)) {
                    if (have.get(j) == dst) { have.set(j, src); }
                    else if (have.get(j) == src) { have.set(j, dst); }
                }
            }
        }
    }

    // A pending move whose source is a register another pending move writes. In a deadlock every
    // move's target is read by some other move, so following those reads ends in a cycle, and
    // any move on the cycle will do.
    cycleMove &self want:Vec<str> have:Vec<str> done:Vec<bool> -> long {
        for k in 0..want.len() {
            if (!done.get(k)) {
                for j in 0..want.len() {
                    if (j != k && !done.get(j) && want.get(j) == have.get(k)) { return k; }
                }
            }
        }
        failStr(stringOf("internal compiler error: the inputs of an `asm` block are blocked, but there is no cycle among them"));
        return 0;
    }

    // Does a move still to be made read the register that move `k` is about to overwrite?
    readsLater &self want:Vec<str> have:Vec<str> done:Vec<bool> k:long -> bool {
        for j in 0..want.len() {
            if (j != k && !done.get(j) && have.get(j) == want.get(k)) { return true; }
        }
        return false;
    }

    // `{rax}` in an asm line becomes the sub-register as wide as the value this block's `in`
    // bound to `rax`. A placeholder naming a register no `in` binds is refused rather than
    // emitted: NASM would read `{rax}` as a decorator and report something that points nowhere
    // near the line the programmer wrote.
    resolveAsmRegs &self p:IRProgram in:Instr line:str -> str {
        out: String;
        i: long = 0;
        while (i < line.len) {
            c: long = charAt(line, i);
            if (c != '{') { out.push(c as char); i = i + 1; }
            else {
                close: long = i + 1;
                while (close < line.len && charAt(line, close) != '}') { close = close + 1; }
                if (close >= line.len) { failStr(format("unclosed register placeholder in an `asm` block\nnote: the line is `{}`\nhelp: a placeholder is a register name in braces, such as `{{rax}}`", line)); }
                want: str = strSlice(line, i + 1, close - i - 1);
                out.pushStr(self.sizedReg(p, in, want, line));
                i = close + 1;
            }
        }
        held: str = "";
        held = keepString(out);
        return held;
    }
    // The name of register `want` at the width of the value an `in` bound to it.
    sizedReg &self p:IRProgram in:Instr want:str line:str -> str {
        for k in 0..in.pieceCount {
            at: long = in.firstPiece + k;
            // An `in` carries the width of the value bound to it. An `out` always writes a whole
            // slot, so only an input decides the sub-register.
            if (p.asmKinds.get(at) == AsmKind.In && nameOf(p.asmRegs.get(at)) == want) {
                return regNameSized(regIndexOf(want), p.asmSizes.get(at));
            }
        }
        failStr(format("placeholder `{{{}}}` in an `asm` block names a register no `in` binds\nnote: the line is `{}`\nhelp: bind it with `in {} <value>`, or write the register without braces", want, line, want));
        return want;
    }

    // A block copy, eight bytes at a time. Every aggregate here is built of 8-byte words and its
    // size is rounded up to one, so there is no tail to handle. Past `UNROLL_COPY_BYTES` it is
    // `rep movsq`, since two instructions per word made up most of a large struct copy's code.
    emitBlockCopy &self in:Instr -> void {
        if (in.imm > UNROLL_COPY_BYTES) {
            self.forceInto(in.a, SCRATCH);
            self.forceInto(in.b, SCRATCH2);
            self.repMovs(in.imm);
            return;
        }
        // A word at a time, with the two addresses read where the allocator put them, so no
        // register has to be borrowed and given back. Eight bytes, not sixteen: what is copied was
        // usually just stored a word at a time (a struct being built), and a 16-byte load across
        // two 8-byte stores is not forwarded from them. The word goes through a general scratch
        // register when one is free; sending every word through `xmm15` (which no allocated value
        // uses) measured 7% more cycles for this compiler compiling itself.
        dst: str = self.intoScratch(in.a, SCRATCH);
        src: str = self.intoScratch(in.b, SCRATCH2);
        // The word goes through whichever scratch neither address took (an address the allocator
        // put in a register leaves its scratch free), and through `xmm15` only when both did.
        via: str = "xmm15";
        if (!strEq(dst, "rax") && !strEq(src, "rax")) { via = "rax"; }
        else if (!strEq(dst, "rdx") && !strEq(src, "rdx")) { via = "rdx"; }
        mv: str = "mov ";
        if (strEq(via, "xmm15")) { mv = "movq "; }
        off: long = 0;
        while (off < in.imm) {
            self.put(mv);
            self.put(via);
            self.put(", [");
            self.put(src);
            if (off != 0) { self.put(" + "); self.putNum(off); }
            self.putLine("]");
            self.put(mv);
            self.put("[");
            self.put(dst);
            if (off != 0) { self.put(" + "); self.putNum(off); }
            self.put("], ");
            self.putLine(via);
            off = off + 8;
        }
    }

    // `memcpy`: `rep movsb`, from `[b]` to `[a]`, as many bytes as its argument says. The
    // allocator keeps nothing live across it in a caller-saved register, so rdi, rsi and rcx are
    // free to take the three operands: a parallel move from wherever they are, each one written
    // once nothing still to be read sits in its register, and a cycle broken through rax.
    emitMemCopy &self p:IRProgram fn:IRFunc in:Instr -> void {
        if (self.emitShortCopy(p, fn, in.a, in.b, p.args.get(in.firstArg))) { return; }
        ts: [Temp; 3] = [in.a, in.b, p.args.get(in.firstArg)];
        to: [long; 3] = [REG_RDI, REG_RSI, REG_RCX];
        via: [long; 3] = [-1, -1, -1];
        done: [bool; 3] = [false, false, false];
        left: long = 3;
        while (left > 0) {
            moved: bool = false;
            for k in 0..3 {
                if (done[k]) { continue; }
                blocked: bool = false;
                for j in 0..3 { if (j != k && !done[j] && self.copySource(ts[j], via[j]) == to[k]) { blocked = true; } }
                if (blocked) { continue; }
                if (via[k] >= 0) {
                    self.put("mov ");
                    self.put(regName64(to[k]));
                    self.put(", ");
                    self.putLine(regName64(via[k]));
                } else { self.forceInto(ts[k], to[k]); }
                done[k] = true;
                left = left - 1;
                moved = true;
            }
            if (!moved) {
                k: long = 0;
                while (done[k]) { k = k + 1; }
                self.put("mov rax, ");
                self.putLine(regName64(self.copySource(ts[k], via[k])));
                via[k] = REG_RAX;
            }
        }
        self.putLine("rep movsb");
    }
    // A `memcpy` whose length is a constant of at most `SHORT_COPY_BYTES`, as moves: `rep movsb`
    // takes tens of cycles to start, more than a short copy takes. The two addresses are read where
    // the allocator put them and the bytes go through a scratch register, as `emitBlockCopy` does.
    // Eight bytes at a time, and a tail as one more move that ends where the copy ends, overlapping
    // the move before it: the two ranges are apart (the builtin's contract), so the bytes written
    // twice are written with the same value. Under eight bytes the same with four, two and one.
    // Answers false, having written nothing, when the length is not such a constant, or when the
    // copy needs a move under four bytes and both general scratch registers hold the addresses.
    emitShortCopy &self p:IRProgram fn:IRFunc dstT:Temp srcT:Temp lenT:Temp -> bool {
        // The length's one definition, a constant, wherever the allocator keeps the value.
        if (gShortCopyOff || lenT == NO_TEMP) { return false; }
        def: long = self.ra.rematAt(lenT);
        if (def < 0 || p.code[fn.firstInstr + def].op != IROp.Const) { return false; }
        n: long = p.code[fn.firstInstr + def].imm;
        if (n < 0 || n > SHORT_COPY_BYTES) { return false; }
        if (n == 0) { return true; }
        // Where each address will be read: its register, or the scratch it is loaded into.
        dr: long = self.ra.regOf(dstT);
        if (dr == SPILLED) { dr = SCRATCH; }
        sr: long = self.ra.regOf(srcT);
        if (sr == SPILLED) { sr = SCRATCH2; }
        via: long = -1;
        if (dr != SCRATCH && sr != SCRATCH) { via = SCRATCH; }
        else if (dr != SCRATCH2 && sr != SCRATCH2) { via = SCRATCH2; }
        if (via < 0 && n < 4) { return false; }
        dst: str = self.intoScratch(dstT, SCRATCH);
        src: str = self.intoScratch(srcT, SCRATCH2);
        w: long = 8;
        if (n < 8) { w = 4; }
        if (n < 4) { w = 2; }
        if (n < 2) { w = 1; }
        off: long = 0;
        while (off < n) {
            at: long = off;
            if (at + w > n) { at = n - w; }
            self.shortMove(dst, src, at, w, via);
            off = at + w;
        }
        return true;
    }
    shortMove &self dst:str src:str off:long w:long via:long -> void {
        reg: str = "xmm15";
        mv: str = "movq ";
        if (w == 4) { mv = "movd "; }
        if (via >= 0) { reg = regNameSized(via, w); mv = "mov "; }
        self.put(mv);
        self.put(reg);
        self.put(", [");
        self.put(src);
        if (off != 0) { self.put(" + "); self.putNum(off); }
        self.putLine("]");
        self.put(mv);
        self.put("[");
        self.put(dst);
        if (off != 0) { self.put(" + "); self.putNum(off); }
        self.put("], ");
        self.putLine(reg);
    }

    // The register an operand of `emitMemCopy` is read from, or -1 for a slot or a value made again.
    copySource &self t:Temp via:long -> long {
        if (via >= 0) { return via; }
        if (self.isRemat(t)) { return -1; }
        r: long = self.ra.regOf(t);
        if (r == SPILLED) { return -1; }
        return r;
    }

    // An atomic, as the one instruction it is. x86-64 is TSO, so a plain `mov` load is an
    // acquire and a plain `mov` store a release; `xchg` with memory is locked on its own, which
    // makes it the sequentially consistent store and the swap; `lock cmpxchg` and `lock xadd`
    // are the compare-and-swap and the fetch-and-add. The address is in a register (rdx when the
    // temp has none); a value that goes through the instruction's own register operand is put in
    // rax, which `cmpxchg` needs for the expected value anyway, and the old value comes back
    // there. A compare-and-swap whose desired value and address both have no register borrows
    // rcx for the first and gives it back.
    emitAtomic &self p:IRProgram in:Instr -> void {
        w: long = widthOf(in.kind);
        op: long = in.imm;
        ar: long = self.intoScratchReg(in.a, SCRATCH2);
        base: str = regName64(ar);
        if (op == BI_ATOMIC_LOAD) {
            if (in.dst == NO_TEMP || self.ra.unread(in.dst)) {
                // Read all the same: the load is the synchronization, whatever it yields.
                self.emitSizedLoad(base, 0, in.kind, SCRATCH);
                return;
            }
            d: long = self.ra.regOf(in.dst);
            if (d != SPILLED) { self.emitSizedLoad(base, 0, in.kind, d); return; }
            self.emitSizedLoad(base, 0, in.kind, SCRATCH);
            self.put("mov ");
            self.put(self.place(in.dst));
            self.putLine(", rax");
            return;
        }
        if (op == BI_ATOMIC_STORE) {
            vr: long = self.intoScratchReg(in.b, SCRATCH);
            self.put("mov ");
            self.putMem(base, 0, w);
            self.put(", ");
            self.putLine(regNameSized(vr, w));
            return;
        }
        // The rest go through rax: the value swapped, added or expected.
        self.forceInto(in.b, SCRATCH);
        borrowed: bool = false;
        if (op == BI_ATOMIC_CAS) {
            dt: Temp = p.args.get(in.firstArg);
            dr: long = self.ra.regOf(dt);
            if (dr == SPILLED) {
                if (ar == SCRATCH2) {
                    self.putLine("push rcx");
                    borrowed = true;
                    dr = REG_RCX;
                } else { dr = SCRATCH2; }
                if (self.isRemat(dt)) { self.materialize(dt, dr); }
                else {
                    self.put("mov ");
                    self.put(regName64(dr));
                    self.put(", ");
                    self.putLine(self.place(dt));
                }
            }
            self.put("lock cmpxchg ");
            self.putMem(base, 0, w);
            self.put(", ");
            self.putLine(regNameSized(dr, w));
            if (borrowed) { self.putLine("pop rcx"); }
        } else {
            if (op == BI_ATOMIC_ADD) { self.put("lock xadd "); } else { self.put("xchg "); }
            self.putMem(base, 0, w);
            self.put(", ");
            self.putLine(regNameSized(SCRATCH, w));
        }
        if (op == BI_ATOMIC_STORE_SC || in.dst == NO_TEMP || self.ra.unread(in.dst)) { return; }
        self.canonicalize(SCRATCH, in.kind);
        self.put("mov ");
        self.put(self.place(in.dst));
        self.putLine(", rax");
    }

    // `size` bytes (whole words) from [rdx] to [rax] by `rep movsq`, `rsi`, `rdi` and `rcx`
    // borrowed for it and given back.
    repMovs &self size:long -> void {
        self.putLine("push rsi");
        self.putLine("push rdi");
        self.putLine("push rcx");
        self.putLine("mov rdi, rax");
        self.putLine("mov rsi, rdx");
        self.put("mov ecx, ");
        self.putNum((size + 7) / 8);
        self.putLine("");
        self.putLine("rep movsq");
        self.putLine("pop rcx");
        self.putLine("pop rdi");
        self.putLine("pop rsi");
    }

    // `[a .. a + imm) = 0`. Up to 128 bytes, one immediate store per word (no register needed
    // beyond the address); past that, `rep stosq`, whose fixed start-up cost the unrolled stores
    // stay under. `rdi` and `rcx` are borrowed for it and given back; `rax` is the scratch the
    // zero lives in. A length that is not a whole number of words ends in narrower stores.
    emitBlockZero &self in:Instr -> void {
        n: long = in.imm;
        if (n <= 0) { return; }
        base: str = "rax";
        off: long = 0;
        if (n <= UNROLL_BYTES) {
            self.forceInto(in.a, SCRATCH);
            while (off + 8 <= n) { self.zeroAt(base, off, "qword"); off = off + 8; }
        } else {
            self.forceInto(in.a, SCRATCH2);
            self.putLine("push rdi");
            self.putLine("push rcx");
            self.putLine("mov rdi, rdx");
            self.put("mov ecx, ");
            self.putNum(n / 8);
            self.putLine("");
            self.putLine("xor eax, eax");
            self.putLine("rep stosq");
            base = "rdi";             // past the last word now
            off = n - n % 8;
        }
        // The tail: past the words just stored, which `rdi` already points at after the
        // `rep stosq` but `rax` (the unrolled stores' base) does not.
        rest: long = n - off;
        k: long = off;
        if (n > UNROLL_BYTES) { k = 0; }
        if (rest >= 4) { self.zeroAt(base, k, "dword"); k = k + 4; rest = rest - 4; }
        if (rest >= 2) { self.zeroAt(base, k, "word"); k = k + 2; rest = rest - 2; }
        if (rest >= 1) { self.zeroAt(base, k, "byte"); }
        if (n > UNROLL_BYTES) {
            self.putLine("pop rcx");
            self.putLine("pop rdi");
        }
    }

    zeroAt &self base:str off:long width:str -> void {
        self.put("mov ");
        self.put(width);
        self.put(" [");
        self.put(base);
        if (off != 0) { self.put(" + "); self.putNum(off); }
        self.putLine("], 0");
    }

    // Put a temp's value in a particular register, whatever the allocator decided.
    forceInto &self t:Temp which:long -> void {
        if (self.isRemat(t)) { self.materialize(t, which); return; }
        where: str = self.place(t);
        if (where == regName64(which)) { return; }
        self.put("mov ");
        self.put(regName64(which));
        self.put(", ");
        self.putLine(where);
    }

    // A comparison sets a flag, which `setcc` turns into 0 or 1 in `al`, widened to the full
    // register so the result is a clean boolean rather than one byte of stale bits.
    // Both operands are canonical words, so one full-width compare orders them correctly at any
    // declared width; only which ordering (below/above or less/greater) depends on the type.
    emitCompare &self in:Instr -> void {
        if (isFloat(in.kind)) { self.emitFloatCompare(in); return; }
        l: str = self.intoScratch(in.a, SCRATCH);
        r: str = "";
        if (self.rightInPlace(in)) { r = self.place(in.b); } else { r = self.rightOperand(in, SCRATCH2); }
        // Into the destination's own register: its low byte set, the rest cleared before the
        // comparison where it holds no operand, else widened after.
        d: long = self.ra.regOf(in.dst);
        if (!gSetInPlaceOff && d != SPILLED && d != REG_RAX && !isXmm(d)) {
            clear: bool = d != self.ra.regOf(in.a) && (in.bIsImm || d != self.ra.regOf(in.b));
            if (clear) {
                self.put("xor ");
                self.put(regNameSized(d, 4));
                self.put(", ");
                self.putLine(regNameSized(d, 4));
            }
            self.put("cmp ");
            self.put(l);
            self.put(", ");
            self.putLine(r);
            self.put("set");
            self.put(setSuffix(in.op, typeInfo(in.kind).unsignedNum));
            self.put(" ");
            self.putLine(regNameSized(d, 1));
            if (!clear) {
                self.put("movzx ");
                self.put(regNameSized(d, 4));
                self.put(", ");
                self.putLine(regNameSized(d, 1));
            }
            return;
        }
        self.put("cmp ");
        self.put(l);
        self.put(", ");
        self.putLine(r);
        self.put("set");
        self.put(setSuffix(in.op, typeInfo(in.kind).unsignedNum));
        self.putLine(" al");
        self.putLine("movzx eax, al");
        if (d == REG_RAX) { return; }
        self.put("mov ");
        self.put(self.place(in.dst));
        self.putLine(", rax");
    }

    // ─── floats ──────────────────────────────────────────────────────────────
    //
    // A float lives where an integer would, as its bits: an `f64`'s 64, an `f32`'s 32 sign-extended
    // (the canonical form of any 4-byte signed value). The allocator keeps a float in one of `xmm8`
    // to `xmm14` when every instruction touching it is one of the float paths below
    // (`RegAlloc.markXmm` decides), and each of those paths can read an operand from an `xmm`
    // register, a general one or a slot. Otherwise the float is its bits in a general register,
    // and an operation moves it into `xmm0`/`xmm1`, computes there, and moves the result back.
    // Arguments and results pass in `xmm0` to `xmm7` (`emitArgs`, the prologue, `Ret`).

    // `xmm<x> <- r` at the float's width.
    toXmm &self x:long r:long single:bool -> void {
        self.toXmmNamed(xmmScratchName(x), r, single);
    }

    toXmmNamed &self dst:str r:long single:bool -> void {
        if (isXmm(r)) {
            if (strEq(dst, regName64(r))) { return; }
            self.put("movaps ");
            self.put(dst);
            self.put(", ");
            self.putLine(regName64(r));
            return;
        }
        if (single) {
            self.put("movd ");
            self.put(dst);
            self.put(", ");
            self.putLine(regNameSized(r, 4));
        } else {
            self.put("movq ");
            self.put(dst);
            self.put(", ");
            self.putLine(regName64(r));
        }
    }

    // A float operand as an `xmm` register's name: its own register, or `xmm<x>` filled from
    // where it is.
    xmmOperand &self t:Temp x:long single:bool -> str {
        r: long = self.ra.regOf(t);
        if (r != SPILLED && isXmm(r)) { return regName64(r); }
        which: long = SCRATCH;
        if (x == 1) { which = SCRATCH2; }
        self.toXmm(x, self.intoScratchReg(t, which), single);
        return xmmScratchName(x);
    }

    // The `xmm` register a temp lives in, or -1.
    xmmOf &self t:Temp -> long {
        r: long = self.ra.regOf(t);
        if (r != SPILLED && isXmm(r)) { return r; }
        return -1;
    }

    // A float in `xmm` register `x` as its canonical word in rax: an `f32` sign-extended.
    xmmToRax &self x:long single:bool -> void {
        if (single) {
            self.put("movd eax, ");
            self.putLine(regName64(x));
            self.putLine("cdqe");
        } else {
            self.put("movq rax, ");
            self.putLine(regName64(x));
        }
    }

    // A copy with a float in an `xmm` register on either side.
    moveFloat &self p:IRProgram in:Instr -> void {
        d: long = self.ra.regOf(in.dst);
        s: long = self.ra.regOf(in.a);
        if (d == s && d != SPILLED) { return; }
        single: bool = floatClass(p.kindOf(in.dst), p.structOf(in.dst)) == 2 || floatClass(p.kindOf(in.a), p.structOf(in.a)) == 2;
        if (d != SPILLED && isXmm(d) && self.isRemat(in.a)) {
            self.materialize(in.a, SCRATCH);
            self.put("movq ");
            self.put(regName64(d));
            self.putLine(", rax");
            return;
        }
        if (d != SPILLED && isXmm(d)) {
            if (s != SPILLED && isXmm(s)) { self.put("movaps "); }
            else { self.put("movq "); }
            self.put(regName64(d));
            self.put(", ");
            self.putLine(self.place(in.a));
            return;
        }
        // From `xmm` into a general register or a slot: the canonical word.
        if (single) {
            self.xmmToRax(s, true);
            self.put("mov ");
            self.put(self.place(in.dst));
            self.putLine(", rax");
            return;
        }
        self.put("movq ");
        self.put(self.place(in.dst));
        self.put(", ");
        self.putLine(regName64(s));
    }

    // `r <- xmm0`, re-extended to the canonical form.
    fromXmm0 &self r:long single:bool -> void {
        if (isXmm(r)) {
            self.put("movaps ");
            self.put(regName64(r));
            self.putLine(", xmm0");
            return;
        }
        if (single) {
            self.put("movd ");
            self.put(regNameSized(r, 4));
            self.putLine(", xmm0");
            self.put("movsxd ");
            self.put(regName64(r));
            self.put(", ");
            self.putLine(regNameSized(r, 4));
        } else {
            self.put("movq ");
            self.put(regName64(r));
            self.putLine(", xmm0");
        }
    }

    // `+ - * /`, and `^` (a negation's sign flip), at the float's width. Into the destination's own
    // `xmm` register when it has one that is not the right operand's: `d = a; d op= b`, one
    // instruction when `a` is already there. Otherwise through `xmm0`.
    emitFloatArith &self in:Instr -> void {
        single: bool = in.kind == Lit.Float;
        mn: str = "addsd ";
        if (in.op == IROp.Sub) { mn = "subsd "; }
        else if (in.op == IROp.Mul) { mn = "mulsd "; }
        else if (in.op == IROp.Div) { mn = "divsd "; }
        if (single) {
            mn = "addss ";
            if (in.op == IROp.Sub) { mn = "subss "; }
            else if (in.op == IROp.Mul) { mn = "mulss "; }
            else if (in.op == IROp.Div) { mn = "divss "; }
        }
        if (in.op == IROp.BXor) { mn = "xorps "; }
        xd: long = self.xmmOf(in.dst);
        if (xd >= 0 && self.ra.regOf(in.b) != xd) {
            sb: str = self.xmmOperand(in.b, 1, single);
            dn: str = regName64(xd);
            ra: long = self.ra.regOf(in.a);
            if (ra != xd) {
                if (ra != SPILLED && isXmm(ra)) { self.toXmmNamed(dn, ra, single); }
                else { self.toXmmNamed(dn, self.intoScratchReg(in.a, SCRATCH), single); }
            }
            self.put(mn);
            self.put(dn);
            self.put(", ");
            self.putLine(sb);
            return;
        }
        sa: str = self.xmmOperand(in.a, 0, single);
        sb: str = self.xmmOperand(in.b, 1, single);
        if (!strEq(sa, "xmm0")) {
            self.put("movaps xmm0, ");
            self.putLine(sa);
        }
        self.put(mn);
        self.put("xmm0, ");
        self.putLine(sb);
        d: long = self.workReg(in.dst);
        self.fromXmm0(d, single);
        self.store(in.dst, 8);
    }

    // `ucomisd` sets ZF, PF and CF; unordered (a NaN) sets all three. So `>` is `seta`, `>=` is
    // `setae` (both false unordered), `<` and `<=` the same with the operands swapped, `==` needs
    // ZF and not PF, `!=` either ZF clear or PF set.
    floatTest &self in:Instr op:IROp single:bool -> void {
        sa: str = self.xmmOperand(in.a, 0, single);
        sb: str = self.xmmOperand(in.b, 1, single);
        cmpMn: str = "ucomisd ";
        if (single) { cmpMn = "ucomiss "; }
        self.put(cmpMn);
        if (op == IROp.CmpLt || op == IROp.CmpLe) { self.put(sb); self.put(", "); self.putLine(sa); }
        else { self.put(sa); self.put(", "); self.putLine(sb); }
    }

    emitFloatCompare &self in:Instr -> void {
        single: bool = in.kind == Lit.Float;
        self.floatTest(in, in.op, single);
        o: IROp = in.op;
        if (o == IROp.CmpEq) { self.putLine("sete al"); self.putLine("setnp dl"); self.putLine("and al, dl"); }
        else if (o == IROp.CmpNe) { self.putLine("setne al"); self.putLine("setp dl"); self.putLine("or al, dl"); }
        else if (o == IROp.CmpGt || o == IROp.CmpLt) { self.putLine("seta al"); }
        else { self.putLine("setae al"); }
        self.putLine("movzx eax, al");
        self.put("mov ");
        self.put(self.place(in.dst));
        self.putLine(", rax");
    }

    // Jump to the label when `a cmpOp b` holds (never the negation: see `compareJump`).
    emitFloatJcc &self in:Instr -> void {
        single: bool = in.kind == Lit.Float;
        self.floatTest(in, in.cmpOp, single);
        o: IROp = in.cmpOp;
        target: str = nameOf(in.name);
        // `imm` 1: jump when the comparison does not hold, a NaN included: the inverted flags.
        if (in.imm == 1) {
            if (o == IROp.CmpEq) {
                self.put("jp ");
                self.putLine(target);
                self.put("jne ");
                self.putLine(target);
                return;
            }
            if (o == IROp.CmpNe) {
                n: long = self.boundsN;
                self.boundsN = n + 1;
                self.put("jp .fpne");
                self.putNum(n);
                self.putLine("");
                self.put("je ");
                self.putLine(target);
                self.put(".fpne");
                self.putNum(n);
                self.putLine(":");
                return;
            }
            if (o == IROp.CmpGt || o == IROp.CmpLt) { self.put("jbe "); } else { self.put("jb "); }
            self.putLine(target);
            return;
        }
        if (o == IROp.CmpEq) {
            n: long = self.boundsN;
            self.boundsN = n + 1;
            self.put("jp .fpne");
            self.putNum(n);
            self.putLine("");
            self.put("je ");
            self.putLine(target);
            self.put(".fpne");
            self.putNum(n);
            self.putLine(":");
            return;
        }
        if (o == IROp.CmpNe) {
            self.put("jp ");
            self.putLine(target);
            self.put("jne ");
            self.putLine(target);
            return;
        }
        if (o == IROp.CmpGt || o == IROp.CmpLt) { self.put("ja "); } else { self.put("jae "); }
        self.putLine(target);
    }

    // `rax` from one numeric type to another with a float on at least one side, as `support::fp`
    // computes it at compile time: `cvt*` rounds by the current mode (nearest), a float to an
    // integer truncates, NaN and out of range give the most negative long (then the low bits, for a
    // narrower integer). An unsigned 64-bit value with the top bit set is halved, keeping the low
    // bit, converted and doubled; a float at or above 2^63 to `u64` has 2^63 taken off first.
    emitFloatConvert &self from:Lit to:Lit -> void {
        if (from == to) { return; }
        n: long = self.boundsN;
        self.boundsN = n + 1;
        if (isFloat(from) && isFloat(to)) {
            if (from == Lit.Float) {
                self.putLine("movd xmm0, eax");
                self.putLine("cvtss2sd xmm0, xmm0");
                self.fromXmm0(SCRATCH, false);
            } else {
                self.putLine("movq xmm0, rax");
                self.putLine("cvtsd2ss xmm0, xmm0");
                self.fromXmm0(SCRATCH, true);
            }
            return;
        }
        if (isFloat(to)) {
            single: bool = to == Lit.Float;
            cvt: str = "cvtsi2sd xmm0, ";
            add: str = "addsd xmm0, xmm0";
            if (single) { cvt = "cvtsi2ss xmm0, "; add = "addss xmm0, xmm0"; }
            if (from == Lit.U64) {
                self.putLine("test rax, rax");
                self.put("js .fpbig"); self.putNum(n); self.putLine("");
                self.put(cvt); self.putLine("rax");
                self.put("jmp .fpdone"); self.putNum(n); self.putLine("");
                self.put(".fpbig"); self.putNum(n); self.putLine(":");
                self.putLine("mov rdx, rax");
                self.putLine("shr rdx, 1");
                self.putLine("and eax, 1");
                self.putLine("or rdx, rax");
                self.put(cvt); self.putLine("rdx");
                self.putLine(add);
                self.put(".fpdone"); self.putNum(n); self.putLine(":");
            } else {
                self.put(cvt); self.putLine("rax");
            }
            self.fromXmm0(SCRATCH, single);
            return;
        }
        // A float to an integer.
        single: bool = from == Lit.Float;
        self.toXmm(0, SCRATCH, single);
        cvt: str = "cvttsd2si rax, xmm0";
        if (single) { cvt = "cvttss2si rax, xmm0"; }
        if (to == Lit.U64) {
            if (single) {
                self.putLine("mov edx, 1593835520");       // 2^63 as an f32
                self.putLine("movd xmm1, edx");
                self.putLine("ucomiss xmm0, xmm1");
            } else {
                self.putLine("mov rdx, 4890909195324358656");   // 2^63 as an f64
                self.putLine("movq xmm1, rdx");
                self.putLine("ucomisd xmm0, xmm1");
            }
            self.put("jae .fpbig"); self.putNum(n); self.putLine("");
            self.putLine(cvt);
            self.put("jmp .fpdone"); self.putNum(n); self.putLine("");
            self.put(".fpbig"); self.putNum(n); self.putLine(":");
            if (single) { self.putLine("subss xmm0, xmm1"); } else { self.putLine("subsd xmm0, xmm1"); }
            self.putLine(cvt);
            self.putLine("btc rax, 63");
            self.put(".fpdone"); self.putNum(n); self.putLine(":");
            return;
        }
        self.putLine(cvt);
        self.canonicalize(SCRATCH, to);
    }

    // Computed in the scratch rather than straight into the destination register: the
    // destination may share a register with the right operand, and moving the left one in first
    // would then destroy the right before it is read.
    emitArith &self in:Instr -> void {
        if (isFloat(in.kind) && (in.op == IROp.Add || in.op == IROp.Sub || in.op == IROp.Mul || in.op == IROp.Div
                                 || in.op == IROp.BXor)) {
            self.emitFloatArith(in);
            return;
        }
        if (in.op == IROp.Div || in.op == IROp.Mod) { self.emitDivide(in); return; }
        if (in.op == IROp.Shl || in.op == IROp.Shr) { self.emitShift(in); return; }
        // An operand may be the value `rax` holds from the instruction just before
        // (`RegAlloc.markRaxPairs`). When it is the right one, a left operand that has to be
        // fetched goes to `rdx` instead, so fetching it cannot destroy the right one.
        bRax: bool = !in.bIsImm && self.ra.regOf(in.b) == REG_RAX;
        lw: long = SCRATCH;
        if (bRax) { lw = SCRATCH2; }
        l: str = self.intoScratch(in.a, lw);
        // A right operand in the frame is read where it lies, except as the second term of a sum
        // written as one `lea` (`threeOperand`), which takes registers only.
        r: str = "";
        dr: long = self.ra.regOf(in.dst);
        if (self.rightInPlace(in) && !(in.op == IROp.Add && dr != SPILLED && !(regName64(dr) == l))) { r = self.place(in.b); }
        else { r = self.rightOperand(in, SCRATCH2); }
        // Straight into the destination register where there is one and it holds nothing this
        // instruction has still to read: two instructions rather than three, and one when the
        // left operand is already sitting there, which after promotion is the common shape of
        // `i = i + 1`. Both operands are materialised above, before anything writes the
        // destination, so the only value that could be destroyed by writing it is the right
        // operand's own.
        d: long = self.ra.regOf(in.dst);
        // The right operand's register taken over by the result (`RegAlloc.takeOperandReg`), the
        // operation being one whose operands may be swapped: done in place, from the left.
        // Both operands one temp, whose register the result took over: `imul r, r`.
        if (!gCommuteOff && d != SPILLED && !isXmm(d) && !in.bIsImm && in.b == in.a && self.ra.regOf(in.a) == d
            && (in.op == IROp.Mul || in.op == IROp.Add || in.op == IROp.BAnd || in.op == IROp.BOr)) {
            dn0: str = regName64(d);
            self.put(mnemonic(in.op));
            self.put(" ");
            self.put(dn0);
            self.put(", ");
            self.putLine(dn0);
            self.canonicalize(d, in.kind);
            return;
        }
        if (d != SPILLED && !in.bIsImm && in.b != in.a && self.ra.regOf(in.b) == d && isCommutative(in.op)) {
            dn: str = regName64(d);
            self.put(mnemonic(in.op));
            self.put(" ");
            self.put(dn);
            self.put(", ");
            self.putLine(l);
            self.canonicalize(d, in.kind);
            return;
        }
        // A product by -1 (`Flow.identity`'s `0 - x` and `~x + 1`): a negation.
        if (d != SPILLED && !isXmm(d) && in.op == IROp.Mul && in.bIsImm && in.bImm == -1) {
            dn1: str = regName64(d);
            if (!(dn1 == l)) {
                self.put("mov ");
                self.put(dn1);
                self.put(", ");
                self.putLine(l);
            }
            self.put("neg ");
            self.putLine(dn1);
            self.canonicalize(d, in.kind);
            return;
        }
        if (d != SPILLED && (in.bIsImm || self.ra.regOf(in.b) != d)) {
            dn: str = regName64(d);
            // Into another register in one instruction where x86 has a three-operand form: an
            // `lea` for a sum or a difference with a constant (it sets no flags, and nothing here
            // reads them), `imul` with an immediate for a product. The low bits are the same as
            // the two-instruction form's, and the result is canonicalized below either way.
            if (!(dn == l) && self.threeOperand(in, dn, l, r)) {
                self.canonicalize(d, in.kind);
                return;
            }
            if (!(dn == l)) {
                self.put("mov ");
                self.put(dn);
                self.put(", ");
                self.putLine(l);
            }
            if (in.op == IROp.Mul && in.bIsImm && (in.bImm == 3 || in.bImm == 5 || in.bImm == 9)) {
                self.mulInPlace(d, in.bImm);
            } else {
                self.put(mnemonic(in.op));
                self.put(" ");
                self.put(dn);
                self.put(", ");
                self.putLine(r);
            }
            self.canonicalize(d, in.kind);
            return;
        }
        // The right operand in `rax` and the destination there too (or in no register): an
        // operation whose operands may be swapped is done in place, any other is computed in
        // `rdx` and copied out.
        if (bRax) {
            if (d == REG_RAX && isCommutative(in.op)) {
                self.put(mnemonic(in.op));
                self.put(" rax, ");
                self.putLine(l);
                self.canonicalize(SCRATCH, in.kind);
                return;
            }
            if (!(l == "rdx")) {
                self.put("mov rdx, ");
                self.putLine(l);
            }
            self.put(mnemonic(in.op));
            self.putLine(" rdx, rax");
            self.canonicalize(SCRATCH2, in.kind);
            self.put("mov ");
            self.put(self.place(in.dst));
            self.putLine(", rdx");
            return;
        }
        if (!(l == "rax")) {
            self.put("mov rax, ");
            self.putLine(l);
        }
        self.put(mnemonic(in.op));
        self.put(" rax, ");
        self.putLine(r);
        self.canonicalize(SCRATCH, in.kind);
        self.put("mov ");
        self.put(self.place(in.dst));
        self.putLine(", rax");
    }

    // `dst = a + x*scale + imm` (`IROp.Lea`): one `lea` into the destination's register, or into
    // `rax` and then its slot. An operand in the frame is fetched into a scratch register first.
    // An operand may be the one value `rax` holds (`markRaxPairs`): the other is then fetched into
    // `rdx`, and a destination in the frame is computed in `rdx` too.
    emitLea &self in:Instr -> void {
        idxRax: bool = self.ra.regOf(in.x) == REG_RAX;
        base: str = "";
        if (in.a != NO_TEMP) {
            if (idxRax) { base = self.intoScratch(in.a, SCRATCH2); } else { base = self.intoScratch(in.a, SCRATCH); }
        }
        idx: str = "rax";
        if (!idxRax) { idx = self.intoScratch(in.x, SCRATCH2); }
        d: long = self.ra.regOf(in.dst);
        inFrame: bool = d == SPILLED || isXmm(d);
        dn: str = "rdx";
        if (!inFrame) { dn = regName64(d); }
        self.put("lea ");
        self.put(dn);
        self.put(", [");
        self.putLeaSum(base, idx, in.scale, in.imm);
        self.putLine("]");
        if (inFrame) {
            self.put("mov ");
            self.put(self.place(in.dst));
            self.putLine(", rdx");
        }
    }
    putLeaSum &self base:str idx:str scale:long disp:long -> void {
        if (base.len > 0) {
            self.put(base);
            self.put(" + ");
        }
        self.put(idx);
        if (scale > 1) {
            self.put("*");
            self.putNum(scale);
        }
        if (disp > 0) { self.put(" + "); self.putNum(disp); }
        else if (disp < 0) { self.put(" - "); self.putNum(0 - disp); }
    }

    // `dst = l op r` written as one instruction, when there is a form for it; false when not.
    threeOperand &self in:Instr dn:str l:str r:str -> bool {
        if (in.op == IROp.Add || (in.op == IROp.Sub && in.bIsImm)) {
            if (in.bIsImm && in.bImm == 0 - 2147483648) { return false; }
            self.put("lea ");
            self.put(dn);
            self.put(", [");
            self.put(l);
            if (in.bIsImm) {
                v: long = in.bImm;
                if (in.op == IROp.Sub) { v = 0 - v; }
                if (v < 0) { self.put(" - "); self.putNum(0 - v); }
                else { self.put(" + "); self.putNum(v); }
            } else {
                self.put(" + ");
                self.put(r);
            }
            self.putLine("]");
            return true;
        }
        // A product by 3, 5 or 9 adds the operand to a scaled copy of itself: one `lea`, a cycle
        // where `imul` takes three.
        if (in.op == IROp.Mul && in.bIsImm && (in.bImm == 3 || in.bImm == 5 || in.bImm == 9)) {
            self.put("lea ");
            self.put(dn);
            self.put(", [");
            self.put(l);
            self.put(" + ");
            self.put(l);
            self.put("*");
            self.putNum(in.bImm - 1);
            self.putLine("]");
            return true;
        }
        if (in.op == IROp.Mul && in.bIsImm) {
            self.put("imul ");
            self.put(dn);
            self.put(", ");
            self.put(l);
            self.put(", ");
            self.putNum(in.bImm);
            self.putLine("");
            return true;
        }
        return false;
    }

    // A variable shift count lives in `cl` and nowhere else: x86 has no `shl r64, r64`. `rcx` is
    // allocatable, so whatever was living there is saved and put back; overwriting it would
    // silently lose a temp the allocator had placed there.
    // `>>` is arithmetic on a signed type and logical on an unsigned one, which is the difference
    // between -8 >> 1 being -4 and being an enormous positive number.
    emitShift &self in:Instr -> void {
        l: str = self.intoScratch(in.a, SCRATCH);
        mn: str = "shl";
        if (in.op == IROp.Shr) {
            mn = "sar";
            if (typeInfo(in.kind).unsignedNum) { mn = "shr"; }
        }
        // A constant count into a register destination: shifted where it lands, since no second
        // operand can be destroyed by writing it.
        d: long = self.ra.regOf(in.dst);
        if (in.bIsImm && d != SPILLED) {
            dn: str = regName64(d);
            if (!(dn == l)) {
                self.put("mov ");
                self.put(dn);
                self.put(", ");
                self.putLine(l);
            }
            self.put(mn);
            self.put(" ");
            self.put(dn);
            self.put(", ");
            self.putNum(in.bImm % 64);
            self.putLine("");
            self.canonicalize(d, in.kind);
            return;
        }
        // A count the allocator left in `rcx` (`hint`) is read where it is, with nothing in `rcx`
        // to save first and put back after; into a register destination other than `rcx`, the
        // value is shifted where it lands.
        if (!gHintsOff && !in.bIsImm && !self.isRemat(in.b) && self.ra.regOf(in.b) == REG_RCX) {
            if (d != SPILLED && d != REG_RCX && !isXmm(d)) {
                dn: str = regName64(d);
                if (!(dn == l)) {
                    self.put("mov ");
                    self.put(dn);
                    self.put(", ");
                    self.putLine(l);
                }
                self.put(mn);
                self.put(" ");
                self.put(dn);
                self.putLine(", cl");
                self.canonicalize(d, in.kind);
                return;
            }
            if (!(l == "rax")) {
                self.put("mov rax, ");
                self.putLine(l);
            }
            self.put(mn);
            self.putLine(" rax, cl");
            self.canonicalize(SCRATCH, in.kind);
            self.put("mov ");
            self.put(self.place(in.dst));
            self.putLine(", rax");
            return;
        }
        if (!(l == "rax")) {
            self.put("mov rax, ");
            self.putLine(l);
        }
        if (in.bIsImm) {
            // `shl rax, N`: the count is an imm8, and a shift past the width is undefined, so
            // it is masked the way the hardware would.
            self.put(mn);
            self.put(" rax, ");
            self.putNum(in.bImm % 64);
            self.putLine("");
        } else {
            self.putLine("push rcx");
            if (self.isRemat(in.b)) { self.materialize(in.b, REG_RCX); }
            else {
                self.put("mov rcx, ");
                self.putLine(self.place(in.b));
            }
            self.put(mn);
            self.putLine(" rax, cl");
            self.putLine("pop rcx");
        }
        self.canonicalize(SCRATCH, in.kind);
        self.put("mov ");
        self.put(self.place(in.dst));
        self.putLine(", rax");
    }

    // `idiv` divides the rdx:rax pair, so the dividend goes in rax with rdx holding its sign:
    // `cqo` for a signed operand, a zeroed rdx (and `div`) for an unsigned one, which gives a
    // different answer once the top bit is set.
    //
    // The divisor is read where it already is. Routing it through rcx would overwrite whatever
    // the allocator had put there; `'0' + (-(n % 10))`, whose zero lived in rcx, then printed
    // every digit ten too high.
    //
    // The 64-bit divide is slow: on this compiler's test machine one every ten cycles where the
    // 32-bit `div` manages one every six, and a few cycles longer from operands to result. When
    // the high halves of both operands are zero, both are below 2^32 and not negative, so the
    // 32-bit unsigned divide of the low halves gives the same quotient and remainder, zero-extended
    // into rax and rdx as the 64-bit one leaves them, and faults on a zero divisor just as it does.
    // So the hot path tests that (`or` of the two, shifted down 32) and divides in 32 bits, and the
    // 64-bit divide waits out of line. An unsigned type no wider than 32 bits is always below
    // 2^32 (its canonical word is zero-extended) and needs no test.
    emitDivide &self in:Instr -> void {
        if (in.bIsImm) { self.emitDivideConst(in); return; }
        unsigned: bool = typeInfo(in.kind).unsignedNum;
        l: str = self.intoScratch(in.a, SCRATCH);
        if (!(l == "rax")) {
            self.put("mov rax, ");
            self.putLine(l);
        }
        r: long = self.ra.regOf(in.b);
        if (unsigned && widthOf(in.kind) <= 4) {
            self.putLine("xor edx, edx");
            self.put("div ");
            self.putDivisor(in.b, 4);
        } else {
            self.putLine("mov rdx, rax");
            self.put("or rdx, ");
            self.putDivisor(in.b, 8);
            self.putLine("shr rdx, 32");
            self.coldSeq = self.coldSeq + 1;
            n: long = self.coldSeq;
            self.put("jne .DV");
            self.putNum(n);
            self.putLine("");
            self.putLine("xor edx, edx");
            self.put("div ");
            self.putDivisor(in.b, 4);
            self.put(".DB");
            self.putNum(n);
            self.putLine(":");
            // Out of line, past the `ret`: the 64-bit divide, then back.
            self.coldLine(".DV", n, ":");
            if (unsigned) { self.cold.pushStr("xor edx, edx\ndiv "); } else { self.cold.pushStr("cqo\nidiv "); }
            if (r != SPILLED) { self.cold.pushStr(regName64(r)); }
            else {
                self.cold.pushStr("qword ");
                self.cold.pushStr(self.place(in.b));
            }
            self.coldNl();
            self.coldLine("jmp .DB", n, "");
        }
        // The quotient is in rax and the remainder in rdx, and either may need re-extending: a
        // narrow signed division wraps at its own width.
        res: long = SCRATCH;
        if (in.op == IROp.Mod) { res = SCRATCH2; }
        self.canonicalize(res, in.kind);
        if (self.keepDiv) { self.divRes = res; return; }
        self.put("mov ");
        self.put(self.place(in.dst));
        self.put(", ");
        self.putLine(regName64(res));
    }

    // The divisor `t` as a `w`-byte operand, ending the line: its register, or its slot.
    putDivisor &self t:Temp w:long -> void {
        r: long = self.ra.regOf(t);
        if (r != SPILLED) { self.putLine(regNameSized(r, w)); return; }
        if (w == 4) { self.put("dword "); } else { self.put("qword "); }
        self.putLine(self.place(t));
    }

    // A division or remainder by a constant `d` (`flow.k` puts it on the instruction only for
    // 2 <= d <= 2^31 - 1) without `idiv`: a power of two as shifts, anything else as the high half
    // of `x * M` shifted, M the scaled reciprocal (Granlund and Montgomery; the multiplier as
    // Hacker's Delight 10-1 and 10-2 compute it, `divMagic`). Exact for every 64-bit dividend; a
    // narrower one is its canonical 64-bit word, whose quotient and remainder are the narrow ones
    // (no constant divisor here can overflow), so one sequence serves every width.
    //
    // The answer is formed in the destination's own register when it has one, so nothing is
    // copied out at the end: every read of `x` comes before the first write of that register,
    // which may therefore be `x`'s own (the allocator hands a dying dividend's register to the
    // result). Otherwise it is formed in rdx (a remainder in rax) and stored. Only rax, rdx and
    // the destination are written, and `x` is read where it lives.
    //
    // A signed quotient rounds toward zero, so a negative `x` is corrected: biased by d - 1
    // before the shift for a power of two, one added for the reciprocal. `flow.k` marks a
    // dividend it proved never negative (`DIV_NONNEG`), and that correction is then left out.
    emitDivideConst &self in:Instr -> void {
        d: long = in.bImm;
        unsigned: bool = typeInfo(in.kind).unsignedNum;
        isMod: bool = in.op == IROp.Mod;
        x: str = self.place(in.a);
        spilled: bool = self.ra.regOf(in.a) == SPILLED;
        dr: long = self.ra.regOf(in.dst);
        into: bool = dr != SPILLED;
        same: bool = into && dr == self.ra.regOf(in.a);
        res: long = REG_RDX;
        if (into) { res = dr; }
        dn: str = regName64(res);
        nonneg: bool = (in.imm & DIV_NONNEG) != 0;
        k: long = exactLog2(d);
        if (k >= 1) {
            if (unsigned) {
                // A logical shift or a mask, where the answer goes.
                self.copyInto(dn, x, same);
                if (isMod) { self.put("and "); self.put(dn); self.put(", "); self.putNum(d - 1); }
                else { self.put("shr "); self.put(dn); self.put(", "); self.putNum(k); }
                self.putLine("");
            } else if (isMod || same || !into) {
                // The bias (d - 1 for a negative x, else 0) in rdx. For k = 1 it is the sign bit
                // alone, one shift.
                self.put("mov rdx, ");
                self.putLine(x);
                if (k > 1) { self.putLine("sar rdx, 63"); }
                self.put("shr rdx, ");
                self.putNum(64 - k);
                self.putLine("");
                if (isMod) {
                    // x - ((x + bias) & -d)
                    self.put("add rdx, ");
                    self.putLine(x);
                    self.put("and rdx, ");
                    self.putNum(0 - d);
                    self.putLine("");
                    if (into) {
                        self.copyInto(dn, x, same);
                        self.put("sub ");
                        self.put(dn);
                        self.putLine(", rdx");
                    } else {
                        self.put("mov rax, ");
                        self.putLine(x);
                        self.putLine("sub rax, rdx");
                        res = REG_RAX;
                        dn = "rax";
                    }
                } else if (same) {
                    // x is the destination: the bias added into it, then the shift.
                    self.put("add ");
                    self.put(dn);
                    self.putLine(", rdx");
                    self.put("sar ");
                    self.put(dn);
                    self.put(", ");
                    self.putNum(k);
                    self.putLine("");
                } else {
                    self.put("add rdx, ");
                    self.putLine(x);
                    self.put("sar rdx, ");
                    self.putNum(k);
                    self.putLine("");
                }
            } else {
                // A quotient into a register of its own: the bias is formed there, then x added.
                self.put("mov ");
                self.put(dn);
                self.put(", ");
                self.putLine(x);
                if (k > 1) { self.put("sar "); self.put(dn); self.putLine(", 63"); }
                self.put("shr ");
                self.put(dn);
                self.put(", ");
                self.putNum(64 - k);
                self.putLine("");
                self.put("add ");
                self.put(dn);
                self.put(", ");
                self.putLine(x);
                self.put("sar ");
                self.put(dn);
                self.put(", ");
                self.putNum(k);
                self.putLine("");
            }
        } else {
            mg: DivMagic = divMagic(d, unsigned);
            self.movImm(REG_RAX, mg.m);
            if (unsigned) { self.put("mul "); } else { self.put("imul "); }
            if (spilled) { self.put("qword "); }
            self.putLine(x);
            // The quotient ends in rdx, except a signed one going into a register of its own,
            // which is finished there.
            qIn: str = "rdx";
            if (unsigned) {
                if (mg.add) {
                    // The multiplier is 65 bits: q = (((x - hi) >> 1) + hi) >> (s - 1).
                    self.put("mov rax, ");
                    self.putLine(x);
                    self.putLine("sub rax, rdx");
                    self.putLine("shr rax, 1");
                    self.putLine("add rdx, rax");
                    if (mg.s > 1) { self.put("shr rdx, "); self.putNum(mg.s - 1); self.putLine(""); }
                } else if (mg.s > 0) { self.put("shr rdx, "); self.putNum(mg.s); self.putLine(""); }
            } else {
                // A multiplier past 2^63 reads as negative: the product is x short, put back.
                if (mg.m < 0) { self.put("add rdx, "); self.putLine(x); }
                if (mg.s > 0) { self.put("sar rdx, "); self.putNum(mg.s); self.putLine(""); }
                if (!nonneg) {
                    // Toward zero: one more for a negative x. x's sign bit, formed in the
                    // destination when the quotient ends there (x is read for the last time).
                    if (into && !isMod) {
                        self.copyInto(dn, x, same);
                        self.put("shr ");
                        self.put(dn);
                        self.putLine(", 63");
                        self.put("add ");
                        self.put(dn);
                        self.putLine(", rdx");
                        qIn = dn;
                    } else {
                        self.put("mov rax, ");
                        self.putLine(x);
                        self.putLine("shr rax, 63");
                        self.putLine("add rdx, rax");
                    }
                }
            }
            if (isMod) {
                // x - q * d
                self.mulInPlace(REG_RDX, d);
                if (into) {
                    self.copyInto(dn, x, same);
                    self.put("sub ");
                    self.put(dn);
                    self.putLine(", rdx");
                } else {
                    self.put("mov rax, ");
                    self.putLine(x);
                    self.putLine("sub rax, rdx");
                    res = REG_RAX;
                    dn = "rax";
                }
            } else if (into && !(qIn == dn)) {
                self.put("mov ");
                self.put(dn);
                self.putLine(", rdx");
            }
        }
        self.canonicalize(res, in.kind);
        if (self.keepDiv) { self.divRes = res; return; }
        if (!into) {
            self.put("mov ");
            self.put(self.place(in.dst));
            self.put(", ");
            self.putLine(dn);
        }
    }

    // `mov dn, x`, unless x is already there.
    copyInto &self dn:str x:str same:bool -> void {
        if (same) { return; }
        self.put("mov ");
        self.put(dn);
        self.put(", ");
        self.putLine(x);
    }

    // Register `r` multiplied by the constant `c` where it is: by 3, 5 or 9 as one `lea` (a
    // single-cycle add of the register to a scaled copy of itself), anything else as `imul`.
    mulInPlace &self r:long c:long -> void {
        rn: str = regName64(r);
        if (c == 3 || c == 5 || c == 9) {
            self.put("lea ");
            self.put(rn);
            self.put(", [");
            self.put(rn);
            self.put(" + ");
            self.put(rn);
            self.put("*");
            self.putNum(c - 1);
            self.putLine("]");
            return;
        }
        self.put("imul ");
        self.put(rn);
        self.put(", ");
        self.put(rn);
        self.put(", ");
        self.putNum(c);
        self.putLine("");
    }
}

// The multiplier and shift that divide by a constant (2 <= d < 2^63, not a power of two) through
// the high half of a 64 x 64 product. Signed: q = hi(x * m) (+ x when m reads negative) >> s,
// plus one when x is negative. Unsigned: q = hi(x * m) >> s, or with `add` (a 65-bit multiplier)
// q = (((x - hi) >> 1) + hi) >> (s - 1). Hacker's Delight, figures 10-1 and 10-2, at 64 bits.

pub divMagic d:long unsigned:bool -> DivMagic {
    one: u64 = 1 as u64;
    two63: u64 = one << (63 as u64);
    ud: u64 = d as u64;
    p: long = 63;
    if (!unsigned) {
        anc: u64 = two63 - one - two63 % ud;      // |nc|, for d > 0
        q1: u64 = two63 / anc;
        r1: u64 = two63 - q1 * anc;
        q2: u64 = two63 / ud;
        r2: u64 = two63 - q2 * ud;
        going: bool = true;
        while (going) {
            p = p + 1;
            q1 = q1 + q1; r1 = r1 + r1;
            if (r1 >= anc) { q1 = q1 + one; r1 = r1 - anc; }
            q2 = q2 + q2; r2 = r2 + r2;
            if (r2 >= ud) { q2 = q2 + one; r2 = r2 - ud; }
            delta: u64 = ud - r2;
            going = q1 < delta || (q1 == delta && r1 == (0 as u64));
        }
        return DivMagic { m: (q2 + one) as long, s: p - 64, add: false };
    }
    add: bool = false;
    nc: u64 = ~(0 as u64) - (((0 as u64) - ud) % ud);
    q1: u64 = two63 / nc;
    r1: u64 = two63 - q1 * nc;
    q2: u64 = (two63 - one) / ud;
    r2: u64 = (two63 - one) - q2 * ud;
    going: bool = true;
    while (going) {
        p = p + 1;
        if (r1 >= nc - r1) { q1 = q1 + q1 + one; r1 = r1 + r1 - nc; }
        else { q1 = q1 + q1; r1 = r1 + r1; }
        if (r2 + one >= ud - r2) {
            if (q2 >= two63 - one) { add = true; }
            q2 = q2 + q2 + one;
            r2 = r2 + r2 + one - ud;
        } else {
            if (q2 >= two63) { add = true; }
            q2 = q2 + q2;
            r2 = r2 + r2 + one;
        }
        delta: u64 = ud - one - r2;
        going = p < 128 && (q1 < delta || (q1 == delta && r1 == (0 as u64)));
    }
    return DivMagic { m: (q2 + one) as long, s: p - 64, add: add };
}

// How many instructions an arm of a branch written as conditional moves may hold, and both arms
// of a diamond together (`markSelects`). Both ways are run, so each costs where it did not before.
local MAX_SEL_ARM: long = 3;
local MAX_SEL_BOTH: long = 4;

// What an arm of such a branch may hold: integer arithmetic that cannot fault and writes only its
// destination (and deleted instructions, which are nothing).
local selOp o:IROp -> bool {
    return o == IROp.Nop || o == IROp.Const || o == IROp.Mov || o == IROp.Add || o == IROp.Sub
        || o == IROp.Mul || o == IROp.BAnd || o == IROp.BOr || o == IROp.BXor || o == IROp.Shl
        || o == IROp.Shr || o == IROp.Lea;
}

// What `selCompute` writes without touching the flags: a constant or a copy (`mov`), and a sum, a
// difference with a constant, a product by 3, 5 or 9 or a shift left by 1 to 3 (`lea`).
local selFlagFree in:Instr -> bool {
    o: IROp = in.op;
    if (o == IROp.Const || o == IROp.Mov || o == IROp.Lea) { return true; }
    if (o == IROp.Add) { return !in.bIsImm || in.bImm != 0 - 2147483648; }
    if (o == IROp.Sub) { return in.bIsImm && in.bImm != 0 - 2147483648; }
    if (o == IROp.Mul) { return in.bIsImm && (in.bImm == 3 || in.bImm == 5 || in.bImm == 9); }
    if (o == IROp.Shl) { return in.bIsImm && in.bImm >= 1 && in.bImm <= 3; }
    return false;
}

// A general register a value of its own may be written to and read from: not rax, which the
// emitter computes in, nor rdx, the other scratch, which holds a value only between its write and
// its read (`RegAlloc.spillScratch`).
local selReg r:long -> bool { return r != SPILLED && r != REG_RAX && r != REG_RDX && !isXmm(r); }

// The instructions of `lo..hi` that are not deleted: how many, the only one (-1: not exactly one),
// the last, and whether all of them leave the flags alone.
local selCount p:IRProgram fn:IRFunc lo:long hi:long -> long {
    c: long = 0;
    for k in lo..hi + 1 { if (p.code[fn.firstInstr + k].op != IROp.Nop) { c = c + 1; } }
    return c;
}
local selOnly p:IRProgram fn:IRFunc lo:long hi:long -> long {
    at: long = -1;
    for k in lo..hi + 1 {
        if (p.code[fn.firstInstr + k].op == IROp.Nop) { continue; }
        if (at >= 0) { return -1; }
        at = k;
    }
    return at;
}
local selLast p:IRProgram fn:IRFunc lo:long hi:long -> long {
    k: long = hi;
    while (k > lo && p.code[fn.firstInstr + k].op == IROp.Nop) { k = k - 1; }
    return k;
}
local selAllFlagFree p:IRProgram fn:IRFunc lo:long hi:long -> bool {
    for k in lo..hi + 1 {
        in: Instr = p.code.get(fn.firstInstr + k);
        if (in.op != IROp.Nop && !selFlagFree(in)) { return false; }
    }
    return true;
}

// How many instructions name each label: branches, and the fault edges and record a `recover`
// handler is reached by.
local countLabelRefs p:IRProgram fn:IRFunc inout refs:HashMap<long, long> -> void {
    for i in 0..fn.instrCount {
        in: Instr = p.code.get(fn.firstInstr + i);
        if (!isBranch(in.op) && in.op != IROp.FaultEdge && in.op != IROp.RecoverPush) { continue; }
        nm: long = in.name as long;
        c: Option<long> = refs.find(nm);
        match c { Some(k) { refs.put(nm, k + 1); } None { refs.put(nm, 1); } }
    }
}

// What a loop's test may have computed for it, and the block before its jump back may hold, for
// either to be written again at another place (`markRotations`): how many instructions.
local MAX_ROT_HEAD: long = 6;
local MAX_ROT_TAIL: long = 4;
local MAX_TAIL_COPIES: long = 3;

// An instruction the emitter writes the same wherever it stands, so it may be written at a second
// place that control reaches with the same registers (`markRotations`). Not a label, a branch, a
// return, a call or an `asm` block, a bounds check (its cold half), a block copy (too long to
// repeat), or a division whose divisor is not a constant (its slow half is out of line).
local repeatable in:Instr -> bool {
    o: IROp = in.op;
    if (o == IROp.Div || o == IROp.Mod) { return in.bIsImm; }
    if (o == IROp.Load) { return !in.paramSeed; }
    return o == IROp.Const || o == IROp.Mov || o == IROp.Store || o == IROp.Add || o == IROp.Sub
        || o == IROp.Mul || o == IROp.BAnd || o == IROp.BOr || o == IROp.BXor || o == IROp.Shl
        || o == IROp.Shr || o == IROp.BNot || isCompare(o) || o == IROp.Convert || o == IROp.PtrLoad
        || o == IROp.Lea || o == IROp.PtrStore || o == IROp.AddrOf || o == IROp.StrAddr || o == IROp.AggSlot;
}

// k when v is 2^k (k >= 1), else -1.
local exactLog2 v:long -> long {
    if (v < 2 || (v & (v - 1)) != 0) { return -1; }
    k: long = 0;
    while ((1 << k) != v) { k = k + 1; }
    return k;
}

// An integer operation whose operands may be swapped.
local isCommutative op:IROp -> bool {
    return op == IROp.Add || op == IROp.Mul || op == IROp.BAnd || op == IROp.BOr || op == IROp.BXor;
}

// ─── names ───────────────────────────────────────────────────────────────────

// Whether this name was declared in this compilation unit and defined in another one.
pub isDeclaredExtern p:IRProgram n:Sym -> bool {
    for i in 0..p.externs.len() {
        if (p.externs.get(i) == n) { return true; }
    }
    return false;
}

// A function marked `@init` or `@fini`.
pub isHook n:Sym -> bool {
    for k in 0..gInitHooks.len() { if (gInitHooks.get(k) == n) { return true; } }
    for k in 0..gFiniHooks.len() { if (gFiniHooks.get(k) == n) { return true; } }
    return false;
}

// `fnLabel` of a name, worked out once per name and kept by its number. The emitter asks for a
// function's label at every call and every reference, and building and interning the text each
// time was a noticeable share of the compile. The answer depends on `gLinkAlias`, which is filled
// from the dependencies' `.klib`s before anything asks.
local var gFnLabels: Vec<str>;
local var gFnLabelSet: Vec<bool>;
pub fnLabelOf n:Sym -> str {
    i: long = n as long;
    if (i < 0) { return fnLabel(nameOf(n)); }
    if (i < gFnLabelSet.len() && gFnLabelSet.get(i)) { return gFnLabels.get(i); }
    while (gFnLabelSet.len() <= i) { gFnLabelSet.push(false); gFnLabels.push(""); }
    l: str = fnLabel(nameOf(n));
    gFnLabels.set(i, l);
    gFnLabelSet.set(i, true);
    return l;
}

// A user function's symbol. `::` becomes `$` so the label is a legal NASM identifier, and the
// `mfn_` prefix means it can never collide with an instruction name.
pub fnLabel name:str -> str {
    // A label written as itself: a call inside another package's body read in for inlining
    // (`irpack`). No source name begins with `=`.
    if (name.len > 0 && charAt(name, 0) == '=') { return strSlice(name, 1, name.len - 1); }
    // An instance function another package compiled: that package's alias for it.
    if (!gLinkAlias.isEmpty()) {
        hit: Option<str> = gLinkAlias.find(name);
        match hit { Some(l) { return l; } None { } }
    }
    s: String;
    s.pushStr("mfn_");
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
    out: str = "";
    out = keepString(s);
    return out;
}

// Argument `i` is passed in register `i`, which is this compiler's own convention rather than
// System V's.
pub regName i:long -> str { return regName64(i); }

// The `xmm` register float argument `k` arrives in, `xmm0` to `xmm7`.
local xmmArgName k:long -> str {
    if (k == 0) { return "xmm0"; }
    if (k == 1) { return "xmm1"; }
    if (k == 2) { return "xmm2"; }
    if (k == 3) { return "xmm3"; }
    if (k == 4) { return "xmm4"; }
    if (k == 5) { return "xmm5"; }
    if (k == 6) { return "xmm6"; }
    return "xmm7";
}

// Where the k-th parameter the registers do not hold is read from in the prologue: above the
// saved `rbp` and the return address, eight bytes each.
local stackParamText k:long -> str {
    out: str = "";
    out = keepString(format("[rbp + {}]", 16 + 8 * k));
    return out;
}

// How far `emitGuard` looks for the test and for the return it leads to.
local GUARD_SPAN: long = 16;

// Whether `t` is one of the values the entry guard holds in a register.
local guardHas gT:Vec<Temp> t:Temp -> bool {
    if (t == NO_TEMP) { return false; }
    for i in 0..gT.len() { if (gT.get(i) == t) { return true; } }
    return false;
}

// Whether the entry guard can compute `in` into a fresh caller-saved register from what it holds
// (`emitGuard` says why these, and no others, are written without a scratch register).
local guardComputes in:Instr gT:Vec<Temp> -> bool {
    if (in.dst == NO_TEMP || guardHas(gT, in.dst) || !guardWord(in.kind)) { return false; }
    o: IROp = in.op;
    if (o == IROp.Const) { return true; }
    if (o == IROp.Load) { return in.isGlobal; }
    if (o == IROp.Mov) { return guardHas(gT, in.a); }
    if (o == IROp.Convert) { return guardWord(in.fromKind) && guardWord(in.toKind) && guardHas(gT, in.a); }
    if (o == IROp.Add || o == IROp.Sub || o == IROp.Mul || o == IROp.BAnd || o == IROp.BOr || o == IROp.BXor) {
        return guardHas(gT, in.a) && (in.bIsImm || guardHas(gT, in.b));
    }
    if (o == IROp.PtrLoad) { return guardHas(gT, in.a) && (in.x == NO_TEMP || guardHas(gT, in.x)); }
    return false;
}

// A value held in a general register as one word: not a float, not an aggregate.
local guardWord k:Lit -> bool { return k != Lit.Void && !isFloat(k) && !byValueAggregate(k); }

// Whether `in` reads one of the values the guard computed, entries `from` to `upto` of its list
// (the parameters come first, and are read anywhere).
local guardReads p:IRProgram in:Instr gT:Vec<Temp> from:long upto:long -> bool {
    for g in from..upto {
        t: Temp = gT.get(g);
        if (in.a == t || (!in.bIsImm && in.b == t) || in.x == t) { return true; }
        for k in 0..in.argCount { if (p.args.get(in.firstArg + k) == t) { return true; } }
        for k in 0..in.pieceCount { if (p.asmVals.get(in.firstPiece + k) == t) { return true; } }
    }
    return false;
}

// The next caller-saved register, from position `from` on, that no argument arrives in (argument
// k arrives in register k, and there are `nInt`), or -1 when none is left.
local guardRegister from:long nInt:long -> long {
    for i in from..CALLER_SAVED_COUNT { if (callerSavedAt(i) >= nInt) { return i; } }
    return -1;
}

// Take move `m` off the prologue's parallel move (`emitSeeds`): the last one takes its place.
local dropSeedMove inout rd:Vec<long> inout rs:Vec<long> inout rt:Vec<str> inout rx:Vec<bool> m:long -> void {
    last: long = rd.len() - 1;
    rd.set(m, rd.get(last));
    rs.set(m, rs.get(last));
    rt.set(m, rt.get(last));
    rx.set(m, rx.get(last));
    rd.pop();
    rs.pop();
    rt.pop();
    rx.pop();
}

// `byte [rax + 8]`: NASM needs the size named wherever the other operand does not imply it.
pub memOperand base:str off:long w:long -> str {
    s: String;
    if (w == 1) { s.pushStr("byte "); }
    if (w == 2) { s.pushStr("word "); }
    if (w == 4) { s.pushStr("dword "); }
    if (w == 8) { s.pushStr("qword "); }
    s.push('[');
    s.pushStr(base);
    if (off != 0) { s.pushStr(" + "); s.pushLong(off); }
    s.push(']');
    return keepString(s);
}

// The pieces a failed check prints, by the label that holds them, so that the `mov rdx` sizing
// each write takes its length from the text itself rather than from a hand count. Put together:
//
//     panic: index 7 out of range for length 3 at app.k:12
//     panic: slice end 5 out of range for length 3 at app.k:14
//     panic: slice start 2 is past slice end 1 at app.k:15
//     panic: slice start 5 out of range for length 3 at app.k:16
//
// which is the same family as the standard library's own reports ("panic: Vec.get: index 7 out
// of range for length 3"). The LLVM back end prints the same words, taken from here.
pub boundsText label:str -> str {
    if (label == "__methBndHead")   { return "panic: index "; }
    if (label == "__methBndMid")    { return " out of range for length "; }
    if (label == "__methRngHead")   { return "panic: slice end "; }
    if (label == "__methStartHead") { return "panic: slice start "; }
    if (label == "__methOrdMid")    { return " is past slice end "; }
    return " at ";
}

// Where one bounds check's `file:line` lives in `.data`.
pub locLabel i:long -> str { return numbered("__methLoc", i); }

// A file global's `.data` symbol. It carries its module, so the same mangling a function label
// uses applies here too.
pub globalSymbol name:str -> str {
    s: String;
    s.pushStr("gbl_");
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
    out: str = "";
    out = keepString(s);
    return out;
}

// ─── lookup tables ───────────────────────────────────────────────────────────
//
// Register names and mnemonics are asked for once per operand the emitter writes, which makes
// them the hottest lookups in the back end. Each is a table built once and indexed by its key,
// not a chain of comparisons that pays one test for every entry ahead of the one it wants. The
// keys here are dense small integers (a register index, an opcode) so the index is the lookup;
// only `regIndexOf`, whose key is the register's spelling, needs to hash.

pub REG_COUNT: long = 14;

// Every register at every width, indexed `r * 4 + widthIndex`. The three families spell it
// differently: the four legacy ones take a prefix and a suffix, the two index ones only a
// prefix, and r8-r15 a suffix, which is why this is a table and not a formula.
local gRegNames: Vec<String> = regNames();
local gRegIndex: HashMap<str, long> = regIndex(gRegNames);
local gMnemonics: Vec<str> = mnemonics();

// 1 -> 0, 2 -> 1, 4 -> 2, 8 -> 3. Anything else is a bug upstream and reads as a full word.
local widthIndex size:long -> long {
    if (size == 1) { return 0; }
    if (size == 2) { return 1; }
    if (size == 4) { return 2; }
    return 3;
}

local regNames -> Vec<String> {
    t: Vec<String>;
    legacy: Vec<str>;   // rax rbx rcx rdx: e/r prefix, l/x suffix
    legacy.push("a"); legacy.push("b"); legacy.push("c"); legacy.push("d");
    index: Vec<str>;    // rdi rsi: e/r prefix, bare at 16 bits, l suffix at 8
    index.push("di"); index.push("si");
    high: Vec<str>;     // r8-r15: b/w/d suffix
    high.push("r8"); high.push("r9"); high.push("r10"); high.push("r11");
    high.push("r12"); high.push("r13"); high.push("r14"); high.push("r15");

    for r in 0..REG_COUNT {
        for w in 0..4 {
            s: String;
            if (r < 4) {
                if (w == 2) { s.pushStr("e"); }
                if (w == 3) { s.pushStr("r"); }
                s.pushStr(legacy.get(r));
                if (w == 0) { s.pushStr("l"); } else { s.pushStr("x"); }
            } else if (r < 6) {
                if (w == 2) { s.pushStr("e"); }
                if (w == 3) { s.pushStr("r"); }
                s.pushStr(index.get(r - 4));
                if (w == 0) { s.pushStr("l"); }
            } else {
                s.pushStr(high.get(r - 6));
                if (w == 0) { s.pushStr("b"); }
                if (w == 1) { s.pushStr("w"); }
                if (w == 2) { s.pushStr("d"); }
            }
            t.push(s);
        }
    }
    return t;
}
// The 64-bit name of each register -> its index: the inverse of `regName64`.
local regIndex names:Vec<String> -> HashMap<str, long> {
    m: HashMap<str, long>;
    for r in 0..REG_COUNT {
        unsafe { m.put(names.at(r * 4 + 3).view(), r); }
    }
    return m;
}

// A register at a given width: `rax`/`eax`/`ax`/`al`.
pub regNameSized r:long size:long -> str {
    if (r >= REG_COUNT) { return regName64(r); }
    unsafe { return gRegNames.at(r * 4 + widthIndex(size)).view(); }
}

pub regName64 r:long -> str {
    if (r >= REG_COUNT) { return xmmAllocName(r - REG_XMM8); }
    unsafe { return gRegNames.at(r * 4 + 3).view(); }
}

// The allocator's `xmm` registers, `xmm8` up, by their index past the general ones.
local xmmAllocName i:long -> str {
    if (i == 0) { return "xmm8"; }
    if (i == 1) { return "xmm9"; }
    if (i == 2) { return "xmm10"; }
    if (i == 3) { return "xmm11"; }
    if (i == 4) { return "xmm12"; }
    if (i == 5) { return "xmm13"; }
    return "xmm14";
}

// The operation scratch registers `xmm0` and `xmm1`.
local xmmScratchName x:long -> str {
    if (x == 0) { return "xmm0"; }
    return "xmm1";
}

// `regNames` builds its spellings from three families keyed on the index (`r < 4` legacy, `r < 6`
// the index registers, the rest `r8` to `r15`), so nothing in it says outright that index 4 is
// `rdi`, while the allocator's caller- and callee-saved sets are written as those indices. This
// runs when the compiler itself is compiled and stops the fold if the two ever describe different
// registers. Only the boundaries the classification actually turns on are worth asserting.
local gRegNumberingChecked: bool = checkRegNumbering();

local checkRegNumbering -> bool {
    if (!strEq(regName64(REG_RAX), "rax")) { panic("register numbering: SCRATCH is not rax"); }
    if (!strEq(regName64(REG_RDX), "rdx")) { panic("register numbering: SCRATCH2 is not rdx"); }
    if (!strEq(regName64(REG_RBX), "rbx")) { panic("register numbering: caller-saved does not start at rbx"); }
    if (!strEq(regName64(REG_R12), "r12")) { panic("register numbering: callee-saved does not start at r12"); }
    if (!strEq(regName64(REG_R15), "r15")) { panic("register numbering: callee-saved does not end at r15"); }
    if (REG_R15 + 1 != REG_COUNT) { panic("REG_COUNT does not match the register numbering"); }
    // relax.k reads registers out of the text by these numbers (`relaxRegSet`).
    for r in 0..REG_SLOTS {
        if (relaxRegSet(regName64(r)) != (1 << r)) { panic("register numbering: relax.k counts the registers differently"); }
    }
    if (relaxRegSet("xmm0") != (1 << REG_SLOTS) || relaxRegSet("rsp") != 0) { panic("register numbering: relax.k counts the scratch registers differently"); }
    return true;
}

// The index a 64-bit register name stands for: the inverse of `regName64`, for the one place a
// register arrives as text: an `asm` block's `in`/`out`.
// The type a function's slot `name` holds, as its loads and stores of it say; Void when none
// does (an `asm` block's output nothing reads). A spliced body's slot has the name its splice
// gave it, which its own loads and stores carry too.
local slotKindIn p:&IRProgram fn:IRFunc name:Sym -> Lit {
    if (name == NO_SYM) { return Lit.Void; }
    for i in 0..fn.instrCount {
        ix: long = fn.firstInstr + i;
        o: IROp = p.code[ix].op;
        if ((o == IROp.Load || o == IROp.Store) && !p.code[ix].isGlobal && p.code[ix].name == name) {
            return p.code[ix].kind;
        }
    }
    return Lit.Void;
}

pub regIndexOf name:str -> long {
    hit: Option<long> = gRegIndex.find(name);
    match hit { Some(r) { return r; } None { } }
    failStr(format("unknown register `{}` in an `asm` block\nhelp: use a 64-bit register name, such as `rax` or `rdi`", name));
    return 0;
}

// The frame is kept a multiple of sixteen so a call made from inside it lands with `rsp` aligned,
// which the ABI requires and some library code assumes without checking.
pub alignUp16 x:long -> long { return (x + 15) / 16 * 16; }
pub alignUp8 x:long -> long { return (x + 7) / 8 * 8; }

pub strBytesLabel i:long -> str { return numbered("strb", i); }
pub blockLabel i:long -> str { return numbered("ctb", i); }
pub strConstLabel i:long -> str { return numbered("strc", i); }

local numbered prefix:str i:long -> str {
    s: String;
    s.pushStr(prefix);
    s.pushLong(i);
    out: str = "";
    out = keepString(s);
    return out;
}

// The condition a comparison sets on. An unsigned type orders by below/above and a signed one by
// less/greater: the same bits, a different answer once the top one is set, which is the whole
// difference between `0xFFFFFFF0 > 1` being true and being false.
pub setSuffix op:IROp unsigned:bool -> str {
    if (op == IROp.CmpEq) { return "e"; }
    if (op == IROp.CmpNe) { return "ne"; }
    if (unsigned) {
        if (op == IROp.CmpLt) { return "b"; }
        if (op == IROp.CmpGt) { return "a"; }
        if (op == IROp.CmpLe) { return "be"; }
        return "ae";
    }
    if (op == IROp.CmpLt) { return "l"; }
    if (op == IROp.CmpGt) { return "g"; }
    if (op == IROp.CmpLe) { return "le"; }
    return "ge";
}

// The x86 mnemonic for a two-operand arithmetic opcode. `mov` for anything with no arithmetic of
// its own, which is what an opcode reaching here that should have been handled elsewhere emits.
pub mnemonic op:IROp -> str { return gMnemonics.get(op as long); }
local mnemonics -> Vec<str> {
    t: Vec<str>;
    i: long = 0;
    while (i <= (IROp.Nop as long)) { t.push("mov"); i = i + 1; }
    t.set(IROp.Add as long,  "add");
    t.set(IROp.Sub as long,  "sub");
    t.set(IROp.Mul as long,  "imul");
    t.set(IROp.BAnd as long, "and");
    t.set(IROp.BOr as long,  "or");
    t.set(IROp.BXor as long, "xor");
    t.set(IROp.Shl as long,  "shl");
    t.set(IROp.Shr as long,  "sar");
    return t;
}

methods Emitter {
    // The finished text. A view, because the caller only writes it out.
    unsafe outView &self -> str { return self.out.view(); }
}

// The directive that emits one value of `bytes` width.
local dataDirective bytes:long -> str {
    if (bytes == 1) { return "db"; }
    if (bytes == 2) { return "dw"; }
    if (bytes == 4) { return "dd"; }
    return "dq";
}

methods Emitter {
    hasFunction &self p:IRProgram name:str -> bool {
        for i in 0..p.funcs.len() {
            if (nameOf(p.funcs.get(i).name) == name) { return true; }
        }
        return false;
    }
}
