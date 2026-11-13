// The IR to x86-64 NASM.
//
// One frame per function, and a spilled temp bounces through `rax`, which is why `rax` and `rdx`
// are never allocated. The convention is the compiler's own: argument `i` in register `i`, result
// in `rax`. Every scalar temp holds a canonical 64-bit word, extended by its own type.
#include <{cfg, ir, regalloc, lower}>
#include <parse::{upstream, registry, types}>
#include <transform::eval>
#include <stdlib::{chars, map, mem, option, fmt, string, vec}>
#include <support::compiler>

// `--lib`: emit an object meant to be linked into a program rather than a program. Every `pub`
// function is kept and exported, and no `_start` is written.
pub var gEmitLibrary: bool = false;

// The symbols another object already defines, read from the `.syms` file its `--lib` build wrote
// (`--use`). Anything named here is not emitted again: it is declared `extern` and the linker
// finds the one copy.
//
// A list of what was actually emitted, rather than a rule re-derived from the source both sides
// parse. The two would have to agree forever, and every place they could drift is a duplicate
// symbol at best and two copies of one piece of storage at worst -- two heaps, two stdout
// buffers, no error anywhere.
pub var gUseSyms: HashMap<str, bool> = map![];

// What this object exported, in the order it was written. `--lib` puts it beside the assembly.
pub var gExportedSyms: Vec<str> = vec![];

// A program linked from packages: the startup initializers of the packages it is built on, in
// the order `_start` must call them (each after everything it depends on).
pub var gStartInits: Vec<str> = vec![];

// A package build's object, beyond what it exports: the generic instances, glue and derived
// methods it stamped (local to it), and its vtables. Recorded in the `.klib` for what a later
// part reuses rather than stamps again.
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
    // A package of one file is named by its path: anything a label cannot hold is `$` and its code.
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

pub struct Emitter {
    out: String,
    ra: RegAlloc,
    slots: HashMap<str, long>,   // variable name -> byte offset from rbp
    frame: long,                 // bytes used so far
    spillAt: Vec<long>,          // spilled temp of this function -> its offset, or 0
    spillBase: Temp,             // ...indexed from here, this function's first temp
    // Every `file:line` a bounds check can report, deduplicated. Collected while the code is
    // emitted and written out with the rest of `.data` afterwards, which is the order
    // `emitProgram` already runs in.
    locs: Vec<Sym>,
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
    aggAt:   Vec<long>,          // aggregate scratch slot -> its offset
    argAt:   Vec<long>,          // argument staging slot -> its offset
    directSeed: Vec<bool>,       // per parameter seed: filled straight from its argument register
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
    relText: HashMap<str, str>,
    numCache: Vec<str>,
    needBounds: bool,            // emit the abort routine only if a check can reach it
    needRange: bool,             // ...and the range-worded copy only if a range check can

    // What `main` reaches (`markReachable`): the functions emitted, the vtables, the globals,
    // the images (a global's bytes, a heap block's) and the string literals.
    live: HashMap<str, bool>,
    liveVt: HashMap<str, bool>,
    liveGlobal: HashMap<str, bool>,
    liveImage: Vec<bool>,
    liveStr: Vec<bool>,
    needHeapCentral: bool          // a reached `asm` block names the allocator's shared state
}

methods Emitter for Default {
    new -> Emitter {
        o: String; r: RegAlloc; cd: String;
        return Emitter { out: o, ra: r, slots: map![], frame: 0, spillAt: vec![], spillBase: 0, locs: vec![], liveExtern: map![], externOrder: vec![], liveExternGlobal: map![], externGlobalOrder: vec![],
                         aggAt: vec![], argAt: vec![], directSeed: vec![], atLast: false, coldSeq: 0,
                         calleeAt: 0, cold: cd, boundsN: 0, heapRegions: 0, frameCache: vec![], globalText: map![], relText: map![], numCache: vec![], needBounds: false, needRange: false,
                         live: map![], liveVt: map![], liveGlobal: map![], liveImage: vec![], liveStr: vec![],
                         needHeapCentral: false };
    }
}

methods Emitter {
    put &self s:str -> void { self.out.pushStr(s); }
    putLine &self s:str -> void { self.out.pushStr(s); self.out.push('\n'); }
    putNum &self v:long -> void { self.out.pushLong(v); }

    // ─── the program ─────────────────────────────────────────────────────────

    emitProgram &self p:IRProgram -> void {
        self.markReachable(p);
        self.emitLinkage(p);
        self.putLine("section .text");
        for f in 0..p.funcs.len() {
            if (self.live.has(nameOf(p.funcs.get(f).name))
                && !gUseSyms.has(fnLabel(nameOf(p.funcs.get(f).name)))) {
                self.emitFunction(p, p.funcs.get(f));
                if (gKlibMode && !p.funcs.get(f).isPub) { gEmittedLocal.push(fnLabel(nameOf(p.funcs.get(f).name))); }
            }
        }
        // A library defines no entry point: the program object it is linked into has one, and
        // two `_start`s do not link.
        if (self.entryHere(p)) { self.emitStart(p); }
        self.emitBoundsFail();
        self.emitData(p);
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
            // compiled the same standard library in, and exporting `pub mem::memcpy` from both
            // is a duplicate definition the linker refuses -- which is what it did.
            if (!(gEmitLibrary || gKlibMode) || !fn.isPub || !self.live.has(nameOf(fn.name))) { continue; }
            if (gUseSyms.has(fnLabel(nameOf(fn.name)))) { continue; }   // another object's already
            self.put("global ");
            self.putLine(fnLabel(nameOf(fn.name)));
            gExportedSyms.push(fnLabel(nameOf(fn.name)));
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
            self.putLine(fnLabel(nameOf(n)));
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

    // Only what `main` can reach is emitted. A function: by a call, by its address taken, by a
    // vtable a trait object is built from, by a name spelled inside an `asm` block, or by a
    // pointer the evaluator laid into `.data`. A global: by a load, a store or its address in a
    // reached function, its label spelled in `asm`, or a pointer in a reached image. An image
    // (a global's bytes, a heap block's): through the global, or a pointer in another reached
    // image. A string literal: by a reached instruction or image. The vtables, the same ways.
    //
    // A program includes far more than it uses: twenty lines through `io` and `vec` lowered to
    // 425 functions and ran a few dozen, and everything else was register-allocated, written
    // out and assembled, at a cost that grew faster than the text. And every one of them carried
    // `ast`'s operator table -- a folded Vec nobody read -- in a 64 KiB-aligned static region.
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
            if (!gReg.isGeneric(nameOf(im.structName)) && gReg.findTrait(nameOf(im.trait.name)) >= 0
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
            // one, and nothing here can see that call. Whole-program pruning is what makes a
            // program's binary small -- `vector` went 170,912 bytes to 66,896 by it -- so this
            // is the flag's doing and never the default.
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
        // Functions and images feed each other -- a function reads a global whose image holds a
        // function's address -- so both queues drain together.
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
                // A direct call names a function this program defines. There is no `extern` in
                // the language, so there is nothing else it could name. An unresolved one used
                // to travel this far and be emitted, and NASM reported the mangled symbol from
                // a line number in generated assembly. It stops here, where the callee still has
                // the name the author wrote.
                // Already defined in another object: referenced, and not walked into, what it
                // reaches is that object's business and was kept when it was built.
                if (in.op == IROp.Call && gUseSyms.has(fnLabel(nameOf(in.name)))) {
                    self.noteExtern(nameOf(in.name));
                    continue;
                }
                if (in.op == IROp.Call && !byName.has(nameOf(in.name))
                    && !isDeclaredExtern(p, in.name)) {
                    enterFnAtDef(fn.name);
                    failStr(format("'{}' is called by '{}' and no function of that name is defined",
                                   nameOf(in.name), nameOf(fn.name)));
                }
                // A call into another object keeps nothing of this one alive, but the symbol has
                // to be declared to NASM: `liveExtern` is what the directive is written from.
                if (in.op == IROp.Call && isDeclaredExtern(p, in.name)) {
                    self.noteExtern(nameOf(in.name));
                }
                if (in.op == IROp.Call || in.op == IROp.FnAddr) { self.reachName(nameOf(in.name), &byName, &work); continue; }
                if (in.op == IROp.VtableAddr) { self.reachVtable(nameOf(in.name), &vtImpl, &byName, &work); continue; }
                if (in.op == IROp.StrLitVal || in.op == IROp.StrAddr) { self.liveStr.set(in.imm, true); continue; }
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
    reachName &self n:str inout byName:HashMap<str, long> inout work:Vec<long> -> void {
        // Defined in another object: referenced and not walked into. The choke point for every
        // way a function is reached that is not a direct call: a vtable slot, a taken address,
        // a pointer the evaluator laid into `.data`. Checking only the call left a vtable holding
        // `dq mfn_string$String_display` with nothing to say the symbol was elsewhere.
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
        t: TraitDef = gReg.traitDef(gReg.findTrait(nameOf(im.trait.name)));
        for k in 0..t.methodCount {
            self.reachName(nameOf(implMethodName(im, gReg.traitMethodAt(t, k).name)), byName, work);
        }
    }
    // A label spelled inside assembly text -- `call mfn_x`, `[rel gbl_y]` -- keeps what it names.
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

    // The cold half of every bounds check: report, then abort. One copy per program, emitted only
    // when a check can reach it.
    //
    // Hand-written because there is nothing to call: the output has to be freestanding, and a
    // program that indexes an array need not have included the stdlib. It touches no allocator and
    // no buffered sink, writing straight to fd 2 -- a failing bounds check is exactly the moment
    // the rest of the program's state stops being worth trusting.
    //
    // Exits 134, the status of a process killed by sigabrt, so a caller testing for a crash still
    // sees one.
    emitBoundsFail &self -> void {
        if (!self.needBounds) { return; }
        self.emitFailReport("__methBoundsFail", "__methBndHead", "__methBndMid");
        if (self.needRange) { self.emitFailReport("__methRangeFail", "__methRngHead", "__methRngMid"); }

        // write(2, rsi, rdx)
        self.putLine("__methBndPut:");
        self.putLine("mov rax, 1");
        self.putLine("mov rdi, 2");
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
        self.putLine("mov r8, 1");
        self.putLine(".bndpos:");
        self.putLine("mov r9, 10");
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
        self.putLine("mov rax, 1");
        self.putLine("mov rdi, 2");
        self.putLine("syscall");
        self.putLine("add rsp, 32");
        self.putLine("ret");
    }

    // `<label>:` rdi = index, rsi = length, rdx:rcx = the {bytes, length} of a `file:line` or
    // zero. Prints head, index, mid, length, ` at <where>` when there is one, a newline; exits
    // 134. One copy per wording a program can reach.
    emitFailReport &self label:str head:str mid:str -> void {
        self.put(label);
        self.putLine(":");
        self.putLine("mov r12, rdi");
        self.putLine("mov r13, rsi");
        self.putLine("mov r14, rdx");
        self.putLine("mov r15, rcx");
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
        self.putLine("mov rdx, 1");
        self.putLine("call __methBndPut");
        self.putLine("mov rdi, 134");
        self.putLine("mov rax, 60");
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

    // One label per file global: with its value when the initializer was a constant, zeroed
    // otherwise -- that one's initializer runs at program start, so a global may still be built
    // from anything an expression can be.
    emitData &self p:IRProgram -> void {
        self.putLine("section .data");
        // The static heap regions first: each is aligned to 64 KiB, which at the head of the
        // section is the section's own alignment and costs nothing inside it. After the strings
        // it cost the padding up to the next boundary -- fifty-four kilobytes of zeros in a
        // program whose one region held three hundred bytes.
        self.emitBlocks(p);
        // Back to `.data`. The regions are in sections of their own name, not `.data.something`:
        // ld merges `.data.*` into `.data`, which put the 64 KiB gap back inside it. And
        // below belongs in the ordinary one.
        self.putLine("section .data");
        self.emitBoundsText();
        self.emitStrings(p);
        // The allocator's shared state: per-size-class central free lists and their locks, plus
        // the arena bump pointer. `stdlib/heap.k` reaches it from inline asm as [rel
        // __heapCentral], so it is the assembler that has to put it there. Zero means unused.
        // Built from packages, it is defined once, by the object whose code names it (the
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

    // A global not declared `var` is read-only: it goes in `.rodata`, where a write the checker
    // did not see -- through a raw pointer read out of it in `unsafe` code -- faults instead of
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

    // An image: rows of bytes, and at each relocation one `dq` naming what the word points at --
    // a string literal's bytes, another block, a global, a vtable, a function -- plus the offset
    // into it, which is how a pointer computed at compile time points at the same `.data` a
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
                if (k == RelocKind.Fn)     { self.put(fnLabel(nameOf(t))); }
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

    // The heap blocks born at compile time. `free` on one of these must do nothing, and it tells
    // a block's origin by the word at its 64 KiB-aligned slab base -- so they are laid out in
    // regions of that alignment whose first word is the static marker `stdlib/heap.k` checks
    // for, 1000, and a block never starts past the region's end: one that would is placed at
    // the head of a fresh region (its tail may run on; only its start is ever handed to `free`).
    emitBlocks &self p:IRProgram -> void {
        used: long = 0;            // bytes of the current region already taken, 0 = no region
        self.heapRegions = 0;
        for i in 0..p.imageFirst.len() {
            if (p.imageIsBlock.get(i) && self.liveImage.get(i)) {
                size: long = p.imageCount.get(i);
                if (used == 0 || used + 16 + size > 65536) {
                    // Its own section, whose alignment the linker satisfies by placing it,
                    // rather than an `align` inside `.data`, which only costs nothing while the
                    // regions are at the head of the section. Linked beside another object's
                    // `.data` they no longer are, and the gap became real: 65 KB of zeros in a
                    // program whose regions held a few hundred bytes.
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

    // The fixed pieces of a bounds-failure message. Their lengths come from the text itself, so
    // editing one cannot leave a `mov rdx, <len>` counting the old one.
    emitBoundsText &self -> void {
        if (!self.needBounds) { return; }
        self.emitTextLabel("__methBndHead");
        self.emitTextLabel("__methBndMid");
        if (self.needRange) {
            self.emitTextLabel("__methRngHead");
            self.emitTextLabel("__methRngMid");
        }
        self.emitTextLabel("__methBndAt");
        // One label per place a check can fail, filled while the code was emitted.
        for i in 0..self.locs.len() {
            self.put(locLabel(i));
            self.put(": db ");
            self.emitBytes(nameOf(self.locs.get(i)));
            self.putLine("");
        }
        self.putLine("__methBndNl: db 10");
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
            if (gReg.isGeneric(nameOf(im.structName))) { i = i + 1; continue; }
            at: long = gReg.findTrait(nameOf(im.trait.name));
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
                self.put(fnLabel(nameOf(implMethodName(im, gReg.traitMethodAt(t, k).name))));
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
        self.putLine("mov rax, 60");
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
        lb: str = fnLabel(nameOf(h));
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
            if (fn.isMain) { return fnLabel(nameOf(fn.name)); }
        }
        return "";
    }

    mainLabel &self p:IRProgram -> str {
        for f in 0..p.funcs.len() {
            fn: IRFunc = p.funcs.get(f);
            if (fn.isMain) { return fnLabel(nameOf(fn.name)); }
        }
        return "mfn_main";
    }

    // ─── one function ────────────────────────────────────────────────────────

    emitFunction &self p:IRProgram fn:IRFunc -> void {
        enterFnAtDef(fn.name);
        self.ra.allocate(p, fn);
        self.slots.clear();
        // The callee-saved registers are pushed after `rbp` is established, so they occupy the
        // first words below it: exactly where slot 1 would otherwise land, and `pop r12` then
        // read back whatever the body had left in that slot. The frame starts below them.
        self.frame = 8 * self.savedCount();
        // Indexed by a temp's position within this function, like the allocator's own table. Sized
        // from `tempCount` alone it had a slot for every temp in the program, and every one that
        // this function never mentions came back SPILLED and took eight bytes of its frame.
        self.spillBase = fn.firstTemp;
        self.spillAt.clear();
        for i in 0..fn.tempCount - fn.firstTemp { self.spillAt.push(0); }

        // Every named variable and every spilled temp needs a slot. Assigned before anything is
        // emitted, because the prologue has to know the frame size up front.
        self.assignSlots(p, fn);

        // A library puts every function in a section of its own, so `ld --gc-sections` can drop
        // the ones the program never reaches. Without it a library costs every binary its whole
        // exported surface (this one is 297 symbols, and it took a 58 KB program to 307 KB)
        // because the object cannot know which of them a consumer will call. It is the linker
        // that can. A program's own object does not need it: `markReachable` already kept only
        // what `main` reaches.
        //
        // The cold half of each bounds check is written after this function's `ret` and so lands
        // in the same section, which is what keeps it with the code that jumps to it.
        if (gEmitLibrary || gKlibMode) {
            self.put("section .text.");
            self.put(fnLabel(nameOf(fn.name)));
            self.putLine(" progbits alloc exec nowrite align=16");
        }
        // Aligned so that a call from here lands with rsp 16-aligned, which the ABI requires and
        // some library code assumes.
        self.putLine("align 16");
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
            gExportedInst.push(fn.name);
        }
        self.put(fnLabel(nameOf(fn.name)));
        self.putLine(":");
        self.putLine("push rbp");
        self.putLine("mov rbp, rsp");
        // The callee-saved pushes come before the frame is cut, so `rsp` is still 16-aligned at
        // every call inside the body. Pushing after `sub rsp` shifts it by eight per register and
        // silently breaks anything that assumes the ABI's alignment.
        self.saveCalleeSaved(true);
        self.put("sub rsp, ");
        self.putNum(self.frameBytes());
        self.putLine("");

        // Parameters arrive in registers and are stored to their slots, so the body reads them by
        // name like any other local.
        //
        // In two passes, because a by-value aggregate arrives as a pointer to the caller's copy
        // and has to be copied into storage of its own. Copying it where it lands would read from
        // an argument register while a later parameter is still sitting in another one, so pass
        // one drains every register to memory and pass two does the copies.
        seeds: long = 0;
        while (seeds < fn.instrCount) {
            in: Instr = p.code.get(fn.firstInstr + seeds);
            if (in.op != IROp.Load || !in.paramSeed) { break; }
            seeds = seeds + 1;
        }
        // A float parameter arrives in the next `xmm` register (the first eight), every other one in
        // the next general register (the first ten), the two counted apart, and what is past them
        // on the stack above the return address, eight bytes each in order: the System V rule,
        // which `emitArgs` follows on the other side. Every register first: a stack parameter is
        // fetched through `rax`, which is itself the first argument's register.
        ii: long = 0;
        fi: long = 0;
        si: long = 0;
        stackAt: Vec<long>;            // each stack parameter's slot above the return address
        stackDest: Vec<str>;
        // A promoted parameter whose register no argument arrives in is filled straight from its
        // argument register, and its slot (which nothing else reads: promotion turned every other
        // access into the temp) is never written. Argument k arrives in register k, so a register
        // numbered at or past the general arguments' count holds none of them.
        nInt: long = 0;
        for i in 0..seeds {
            sd: Instr = p.code.get(fn.firstInstr + i);
            if (floatClass(sd.kind, sd.structName) == 0) { nInt = nInt + 1; }
        }
        self.directSeed.clear();
        for i in 0..seeds { self.directSeed.push(false); }
        for i in 0..seeds {
            in: Instr = p.code.get(fn.firstInstr + i);
            dest: str = "";
            if (byValueAggregate(in.kind)) { dest = self.argSlot(i); }
            else { dest = self.slotOf(in.name); }
            if (in.promoted && in.dst != NO_TEMP && !byValueAggregate(in.kind)) {
                r: long = self.ra.regOf(in.dst);
                if (r != SPILLED && r >= nInt) {
                    if (floatClass(in.kind, in.structName) > 0 && fi < FLOAT_ARG_REGS) { dest = regName64(r); self.directSeed.set(i, true); }
                    else if (floatClass(in.kind, in.structName) == 0 && ii < INT_ARG_REGS) {
                        dest = regName64(r);
                        self.directSeed.set(i, true);
                    }
                }
            }
            if (floatClass(in.kind, in.structName) > 0) {
                if (fi < FLOAT_ARG_REGS) {
                    self.put("movq ");
                    self.put(dest);
                    self.put(", xmm");
                    self.putNum(fi);
                    self.putLine("");
                    fi = fi + 1;
                    continue;
                }
            } else if (ii < INT_ARG_REGS) {
                self.put("mov ");
                self.put(dest);
                self.put(", ");
                self.putLine(regName(ii));
                ii = ii + 1;
                continue;
            }
            stackAt.push(si);
            stackDest.push(dest);
            si = si + 1;
        }
        for k in 0..stackAt.len() {
            self.put("mov rax, [rbp + ");
            self.putNum(16 + 8 * stackAt.get(k));
            self.putLine("]");
            self.put("mov ");
            self.put(stackDest.get(k));
            self.putLine(", rax");
        }
        for i in 0..seeds {
            in: Instr = p.code.get(fn.firstInstr + i);
            if (byValueAggregate(in.kind)) {
                self.put("mov rdx, ");
                self.putLine(self.argSlot(i));
                self.copyFromPointer(self.slotOffsetOf(in.name), in.imm);
            }
        }

        self.cold.clear();
        // A `ret` that is the body's last instruction falls into the epilogue rather than jumping to it.
        lastReal: long = fn.instrCount - 1;
        while (lastReal >= 0 && p.code.get(fn.firstInstr + lastReal).op == IROp.Nop) { lastReal = lastReal - 1; }
        self.boundsN = 0;
        i: long = 0;
        while (i < fn.instrCount) {
            in: Instr = p.code.get(fn.firstInstr + i);
            // A check that jumps over its own panic (`if (i < len) goto ok; panic(...); ok:`) is
            // written the other way round, jumping to the panic, and the panic goes out of line
            // past the `ret` with the bounds failures: the path that runs falls straight through.
            // Only the text moves; the allocation is the IR's, which is why this is here.
            if (in.op == IROp.Jcc && !isFloat(in.kind)) {
                e: long = self.coldRun(p, fn, i);
                if (e >= 0) {
                    j: long = i + 1;
                    while (p.code.get(fn.firstInstr + j).op == IROp.Nop) { j = j + 1; }
                    inv: Instr = in;
                    inv.cmpOp = negateCompare(in.cmpOp);
                    labeled: bool = p.code.get(fn.firstInstr + j).op == IROp.Label;
                    if (labeled) { inv.name = p.code.get(fn.firstInstr + j).name; }
                    else {
                        self.coldSeq = self.coldSeq + 1;
                        inv.name = internString(format(".CR{}", self.coldSeq));
                    }
                    self.emitInstr(p, fn, inv);
                    hot: String = take(&self.out);
                    if (!labeled) { self.put(nameOf(inv.name)); self.putLine(":"); }
                    for k in j..e + 1 { self.emitInstr(p, fn, p.code.get(fn.firstInstr + k)); }
                    text: String = take(&self.out);
                    self.out = take(&hot);
                    unsafe { self.cold.pushStr(text.view()); }
                    i = e + 1;
                    continue;
                }
            }
            // A seed is normally not emitted: the prologue has already put the argument in the
            // parameter's slot and the body reads it by name. A promoted one is emitted, and is
            // the single load that fills the temp the body now reads instead.
            direct: bool = i < self.directSeed.len() && self.directSeed.get(i);
            self.atLast = i == lastReal;
            if ((!(in.op == IROp.Load && in.paramSeed) || in.promoted) && !direct) { self.emitInstr(p, fn, in); }
            self.atLast = false;
            i = i + 1;
        }

        self.put(".end");
        self.put(fnLabel(nameOf(fn.name)));
        self.putLine(":");
        self.put("add rsp, ");
        self.putNum(self.frameBytes());
        self.putLine("");
        self.saveCalleeSaved(false);
        self.putLine("pop rbp");
        self.putLine("ret");
        // Past the `ret`: the cold halves of this function's bounds checks. None of them returns.
        unsafe { self.put(self.cold.view()); }
        self.cold.clear();
    }

    // After the branch at `i`: a run that starts with a label, holds no other label and no branch,
    // and ends in a call that never returns, followed directly by the branch's own target. The
    // index of that call, or -1.
    coldRun &self p:IRProgram fn:IRFunc i:long -> long {
        target: Sym = p.code.get(fn.firstInstr + i).name;
        j: long = i + 1;
        while (j < fn.instrCount && p.code.get(fn.firstInstr + j).op == IROp.Nop) { j = j + 1; }
        if (j >= fn.instrCount) { return -1; }
        // The run may start with a label of its own, or (when no branch names one) without.
        k: long = j;
        if (p.code.get(fn.firstInstr + j).op == IROp.Label) { k = j + 1; }
        while (k < fn.instrCount) {
            in: Instr = p.code.get(fn.firstInstr + k);
            if (in.op == IROp.Label || isTerminator(in.op)) { return -1; }
            if (in.op == IROp.Call && in.noReturn) {
                m: long = k + 1;
                while (m < fn.instrCount && p.code.get(fn.firstInstr + m).op == IROp.Nop) { m = m + 1; }
                if (m < fn.instrCount && p.code.get(fn.firstInstr + m).op == IROp.Label
                    && p.code.get(fn.firstInstr + m).name == target) { return k; }
                return -1;
            }
            k = k + 1;
        }
        return -1;
    }

    // The frame, padded so that `rsp` stays 16-aligned once the saved registers are counted:
    // `push rbp` and each callee-saved push move it by eight apiece.
    frameBytes &self -> long {
        saved: long = self.savedCount();
        n: long = alignUp16(self.frame);
        if ((saved % 2) == 1) { n = n + 8; }   // an odd number of pushes needs eight more
        return n;
    }

    // How many callee-saved registers this function's prologue pushes.
    savedCount &self -> long {
        n: long = 0;
        for i in 0..CALLEE_SAVED_COUNT {
            if (self.ra.usedCallee.get(calleeSavedAt(i))) { n = n + 1; }
        }
        return n;
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
    assignSlots &self p:IRProgram fn:IRFunc -> void {
        for i in 0..fn.instrCount {
            in: Instr = p.code.get(fn.firstInstr + i);
            if ((in.op == IROp.Load || in.op == IROp.Store || in.op == IROp.AddrOf)
                && !in.isGlobal) {
                if (in.name != NO_SYM && !self.slots.has(nameOf(in.name))) {
                    self.frame = self.frame + alignUp8(p.slotBytesOf(in.name));
                    self.slots.put(nameOf(in.name), self.frame);
                }
            }
            // An `asm` block's `out` names a slot even when nothing reads it afterwards (a
            // `syscall` builtin's result dropped, whose load the optimizer removed): without one
            // here the store landed at `[rbp - 0]`, over the saved frame pointer.
            if (in.op == IROp.Asm) {
                for k in 0..in.pieceCount {
                    at: long = in.firstPiece + k;
                    nm: Sym = p.asmNames.get(at);
                    if (p.asmKinds.get(at) == AsmKind.Out && nm != NO_SYM && !self.slots.has(nameOf(nm))) {
                        self.frame = self.frame + alignUp8(p.slotBytesOf(nm));
                        self.slots.put(nameOf(nm), self.frame);
                    }
                }
            }
        }
        // Scratch space for aggregate results, one block per call site that needs one. `AggSlot`
        // names a position in this list, not a size: an index into it, which is what makes
        // splicing a body elsewhere have to offset those indices.
        //
        // The list is program-wide, so only the entries this function's own instructions name may
        // take frame space. Reserving all of them gave every function, however small, a frame as
        // big as every aggregate in the program put together (58KB for a two-line accessor) and
        // anything recursive then ran out of stack rather than returning an answer.
        self.aggAt.clear();
        for i in 0..p.aggSlots.len() { self.aggAt.push(0); }
        for i in 0..fn.instrCount {
            in: Instr = p.code.get(fn.firstInstr + i);
            if (in.op == IROp.AggSlot && self.aggAt.get(in.imm) == 0) {
                self.frame = self.frame + alignUp8(p.aggSlots.get(in.imm));
                self.aggAt.set(in.imm, self.frame);
            }
        }

        // One slot for the callee of an indirect call. It has to be parked somewhere before the
        // argument registers are written, because argument `k` goes in register `k` and a callee
        // sitting in one of those would be overwritten before it could be called.
        self.frame = self.frame + 8;
        self.calleeAt = self.frame;

        // Somewhere to stage a call's arguments when one of them lives in a register an earlier
        // argument is about to overwrite. As wide as the widest call this function makes, so the
        // hazardous ones have room and the rest cost nothing but frame bytes.
        self.argAt.clear();
        widest: long = 0;
        for i in 0..fn.instrCount {
            in: Instr = p.code.get(fn.firstInstr + i);
            n: long = in.argCount;
            // The prologue parks a by-value aggregate parameter here too, so there must be a
            // slot for every parameter as well as for the widest call.
            if (in.op == IROp.Load && in.paramSeed) { n = i + 1; }
            if (n > widest) { widest = n; }
        }
        for i in 0..widest {
            self.frame = self.frame + 8;
            self.argAt.push(self.frame);
        }

        // Only this function's temps. A spill slot for every temp in the program is what made a
        // frame grow with the size of the program rather than with the size of the function.
        t: Temp = fn.firstTemp;
        while (t < fn.tempCount) {
            if (self.ra.regOf(t) == SPILLED) {
                self.frame = self.frame + 8;
                self.spillAt.set(t - self.spillBase, self.frame);
            }
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
        hit: Option<long> = self.slots.find(nameOf(name));
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

    // Where a named variable lives. A global is reached through its own label; Rip-relative, so
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
        hit: Option<long> = self.slots.find(nameOf(name));
        off: long = 0;
        match hit { Some(o) { off = o; } None { } }
        return self.frameText(off);
    }

    // `lea <dst>, <operand>`: straight into the destination register where there is one.
    //
    // All five address-producing instructions computed into `rax` and then copied out, which in
    // the hottest loop in the benchmark suite read `lea rax, [rbp-104]` / `mov rbx, rax` /
    // `mov rax, rbx`: three instructions to take one address. `lea` reads only its base register
    // (`rbp` or `rip`) never its destination, so writing the destination first can destroy
    // nothing the instruction still needs. A spilled destination still goes through the scratch,
    // because a `lea` cannot write to memory.
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

    // Where a temp lives: its register, or its spill slot.
    place &self t:Temp -> str {
        if (t == NO_TEMP) { return "rax"; }      // a missing operand: nothing sensible to name
        r: long = self.ra.regOf(t);
        if (r != SPILLED) { return regName64(r); }
        return self.frameText(self.spillAt.get(t - self.spillBase));
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
    // This is several times per instruction (every operand that lives in a frame slot) and it
    // used to build a `String` and intern it each time: an allocation, a hash and a map lookup to
    // produce one of a few hundred distinct strings, hundreds of thousands of times a build. An
    // offset is a multiple of eight and small, so the cache is a vector indexed by it and the
    // answer costs one bounds-checked read. The text does not depend on which function is being
    // emitted (an offset from `rbp` means the same thing in all of them) so it is never
    // invalidated.
    frameText &self off:long -> str {
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

    // A small immediate as text, kept. `format` here built a String and interned it once per
    // immediate operand (twenty-four thousand of them in this compiler's own output) to spell
    // numbers that are almost all between -128 and 1024.
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
        self.put("mov ");
        self.put(regName64(which));
        self.put(", ");
        self.putLine(self.place(t));
        return which;
    }

    // ─── one instruction ─────────────────────────────────────────────────────

    emitInstr &self p:IRProgram fn:IRFunc in:Instr -> void {
        // An instruction the optimizer deleted. It stays in the list so no function's run moves;
        // nothing is emitted for it.
        if (in.op == IROp.Nop) { return; }
        // A fused compare-and-branch: what `Jz` on a comparison means, without the `setcc`, the
        // widening and the second compare against zero that spelling it as a value costs.
        if (in.op == IROp.Jcc) {
            if (isFloat(in.kind)) { self.emitFloatJcc(in); return; }
            l: str = self.intoScratch(in.a, SCRATCH);
            r: str = self.rightOperand(in, SCRATCH2);
            self.put("cmp ");
            self.put(l);
            self.put(", ");
            self.putLine(r);
            self.put("j");
            self.put(setSuffix(in.cmpOp, typeInfo(in.kind).unsignedNum));
            self.put(" ");
            self.putLine(nameOf(in.name));
            return;
        }
        if (in.op == IROp.Label) {
            self.put(nameOf(in.name));
            self.putLine(":");
            return;
        }
        if (in.op == IROp.Const) {
            // A float constant for an `xmm` register: its bits through rax.
            xc: long = self.xmmOf(in.dst);
            if (xc >= 0) {
                self.put("mov rax, ");
                self.putNum(in.imm);
                self.putLine("");
                self.put("movq ");
                self.put(regName64(xc));
                self.putLine(", rax");
                return;
            }
            // A literal already is the canonical word, so there is nothing to extend, but it
            // goes through the scratch when the destination is a slot: `mov [rbp - n], imm` names
            // no operand size, and a memory destination takes only a 32-bit immediate anyway.
            self.put("mov ");
            self.put(regName64(self.workReg(in.dst)));
            self.put(", ");
            self.putNum(in.imm);
            self.putLine("");
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
            self.putLine(fnLabel(nameOf(fn.name)));
            return;
        }
        if (in.op == IROp.RetVoid) {
            if (self.atLast) { return; }
            self.put("jmp .end");
            self.putLine(fnLabel(nameOf(fn.name)));
            return;
        }
        if (in.op == IROp.Jmp) {
            self.put("jmp ");
            self.putLine(nameOf(in.name));
            return;
        }
        if (in.op == IROp.Jz) {
            self.put("cmp ");
            if (self.ra.regOf(in.a) != SPILLED) { self.put(self.place(in.a)); }
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
            base: str = self.intoScratch(in.a, SCRATCH);
            xp: long = self.xmmOf(in.dst);
            if (xp >= 0) {
                if (in.kind == Lit.Float) { self.put("movss "); } else { self.put("movsd "); }
                self.put(regName64(xp));
                self.put(", ");
                self.putLine(memOperand(base, in.imm, widthOf(in.kind)));
                return;
            }
            d: long = self.ra.regOf(in.dst);
            if (d != SPILLED) { self.emitSizedLoad(base, in.imm, in.kind, d); return; }
            self.emitSizedLoad(base, in.imm, in.kind, SCRATCH2);
            self.put("mov ");
            self.put(self.place(in.dst));
            self.putLine(", rdx");
            return;
        }
        if (in.op == IROp.PtrStore) {
            base: str = self.intoScratch(in.a, SCRATCH);
            xv: long = self.xmmOf(in.b);
            if (xv >= 0 && !in.bIsImm) {
                if (in.kind == Lit.Float) { self.put("movss "); } else { self.put("movsd "); }
                self.put(memOperand(base, in.imm, widthOf(in.kind)));
                self.put(", ");
                self.putLine(regName64(xv));
                return;
            }
            vr: long = self.intoScratchReg(in.b, SCRATCH2);
            self.put("mov ");
            self.put(memOperand(base, in.imm, widthOf(in.kind)));
            self.put(", ");
            self.putLine(regNameSized(vr, widthOf(in.kind)));
            return;
        }
        if (in.op == IROp.StrLitVal) {
            self.leaInto(in.dst, self.relOperand(strConstLabel(in.imm)));
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
        if (in.op == IROp.Asm) { self.emitAsmBlock(p, in); return; }
        if (in.op == IROp.Call) { self.emitCall(p, in); return; }
        if (in.op == IROp.CallIndirect) { self.emitCallIndirect(p, in); return; }
        if (in.op == IROp.FnAddr) {
            self.leaInto(in.dst, self.relOperand(fnLabel(nameOf(in.name))));
            return;
        }
        if (in.op == IROp.VtableAddr) {
            self.leaInto(in.dst, self.relOperand(nameOf(in.name)));
            return;
        }
        if (in.op == IROp.BNot) {
            v: str = self.intoScratch(in.a, SCRATCH);
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

    // A load of exactly the pointee's width, extended into the full scratch register. Reading
    // eight bytes for every load is what made `f[i]` on a `[u8]` answer with eight characters at
    // once, so a format string's first `{` was never found; writing eight is what made a one-byte
    // store trample the seven bytes after it.
    emitSizedLoad &self base:str off:long k:Lit r:long -> void {
        w: long = widthOf(k);
        if (w >= 8) {
            self.put("mov ");
            self.put(regName64(r));
            self.put(", ");
            self.putLine(memOperand(base, off, 8));
            return;
        }
        if (w == 4) {
            // A 32-bit destination register zeroes the upper half on its own; a signed source
            // has to say so, or `-1 as long` reads as four billion.
            if (typeInfo(k).unsignedNum) {
                self.put("mov ");
                self.put(regNameSized(r, 4));
                self.put(", ");
                self.putLine(memOperand(base, off, 4));
            } else {
                self.put("movsxd ");
                self.put(regName64(r));
                self.put(", ");
                self.putLine(memOperand(base, off, 4));
            }
            return;
        }
        if (typeInfo(k).unsignedNum) { self.put("movzx "); }
        else                         { self.put("movsx "); }
        self.put(regName64(r));
        self.put(", ");
        self.putLine(memOperand(base, off, w));
    }

    // `x as T`: the same value at a different width, which is one instruction and not the
    // two-operand arithmetic the fallthrough would treat it as. Widening a signed source
    // sign-extends and an unsigned one zero-extends, because that is the difference between
    // `-1 as long` being -1 and being 4294967295. Narrowing keeps the low bytes and needs no
    // instruction at all: the destination is read at its own width from here on.
    // Unless (unsigned) index < length, say what happened and abort. The in-range path is one
    // compare and one not-taken branch; the reporting is all on the cold side of it, past the
    // function's `ret`. Unsigned, so a negative index is an enormous one and fails the same test.
    //
    // A range bound (`imm` 1) is inclusive -- `hi <= len`, `lo <= hi` -- and is worded
    // differently, because exceeding a bound and writing one backwards are different mistakes.
    emitBounds &self in:Instr -> void {
        range: bool = in.imm == 1;
        n: long = self.boundsN;
        self.boundsN = n + 1;
        self.needBounds = true;
        if (range) { self.needRange = true; }

        idx: str = self.intoScratch(in.a, SCRATCH);
        self.put("mov rax, ");
        self.putLine(idx);
        self.put("cmp rax, ");
        self.putLine(self.place(in.b));
        if (range) { self.put("ja "); } else { self.put("jae "); }
        self.put(".boundsfail");
        self.putNum(n);
        self.putLine("");

        // The report, out of line. The length goes to rsi first: either value may itself be
        // living in rdi, and writing rdi first would destroy a length sitting there. The index
        // then comes from rax, which still holds it from the compare.
        self.coldLine(".boundsfail", n, ":");
        self.cold.pushStr("mov rsi, ");
        self.cold.pushStr(self.place(in.b));
        self.coldNl();
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
            self.cold.pushStr("mov rcx, ");
            self.cold.pushLong(text.len);
            self.coldNl();
        }
        self.cold.pushStr("call ");
        if (range) { self.cold.pushStr("__methRangeFail"); }
        else       { self.cold.pushStr("__methBoundsFail"); }
        self.coldNl();
    }

    // The label a location's bytes get, adding it on first sighting. Deduplicated, because one
    // line indexed in a loop is one check emitted once but every `[` in a file is its own entry.
    locIndex &self s:Sym -> long {
        for i in 0..self.locs.len() {
            if (self.locs.get(i) == s) { return i; }
        }
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

    // Arguments go to their registers, then the call, then the result comes out of rax.
    emitCall &self p:IRProgram in:Instr -> void {
        pushed: long = self.emitArgs(p, in, false);
        self.put("call ");
        self.putLine(fnLabel(nameOf(in.name)));
        self.dropStackArgs(pushed);
        self.callResult(p, in);
    }

    // A call's result into its destination: from `xmm0` for a float (straight into the
    // destination's own `xmm` register when it has one), from rax otherwise.
    callResult &self p:IRProgram in:Instr -> void {
        if (in.dst == NO_TEMP) { return; }
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
    // value is still sitting in an earlier one's register -- `g(a, b)` with `b` in rbx is exactly
    // that, and once rbx holds `a` the old value is gone. That is the only hazard, and it is
    // checkable: a spilled source cannot be clobbered by a register write at all, and a source in
    // a register is only at risk when that register is an earlier argument's. When neither holds
    // the values go straight to their registers, which is most calls; otherwise they go through
    // staging slots first, where no register write can reach them.
    // Returns how many bytes of stack arguments it pushed, for the caller to drop after the call.
    emitArgs &self p:IRProgram in:Instr indirect:bool -> long {
        // Where each argument goes: a float to the next of the first eight `xmm` registers, the
        // rest to the next of the first ten general ones, and past those to the stack, eight bytes
        // each in order (System V's rule for what the registers do not hold). A source still in a
        // general register that an earlier argument has already been written to is the hazard,
        // and stages everything.
        staged: bool = false;
        k: long = 0;
        ints: long = 0;
        floats: long = 0;
        stacked: long = 0;
        while (k < in.argCount) {
            t: Temp = p.args.get(in.firstArg + k);
            r: long = self.ra.regOf(t);
            if (r != SPILLED && r < ints) { staged = true; }
            if (floatClass(p.kindOf(t), p.structOf(t)) > 0) {
                if (floats < FLOAT_ARG_REGS) { floats = floats + 1; } else { stacked = stacked + 1; }
            } else if (ints < INT_ARG_REGS) { ints = ints + 1; }
            else { stacked = stacked + 1; }
            k = k + 1;
        }
        if (staged) {
            k = 0;
            while (k < in.argCount) {
                self.moveToSlot(self.argSlot(k), p.args.get(in.firstArg + k));
                k = k + 1;
            }
        }
        // The callee address lands in memory before any argument register is written, so it can
        // never be one of the things clobbered.
        if (indirect) { self.moveToSlot(self.calleeSlot(), in.a); }
        // The stack arguments next, through the scratch, before any argument register is written:
        // the block is a multiple of sixteen, so `rsp` is still aligned at the call. Every frame
        // operand is `rbp`-relative, so moving `rsp` moves none of them.
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
            at: str = keepString(format("qword [rsp + {}]", 8 * stacked));
            if (staged) {
                self.put("mov rax, ");
                self.putLine(self.argSlot(k));
                self.put("mov ");
                self.put(at);
                self.putLine(", rax");
            } else {
                self.moveToSlot(at, t);
            }
            stacked = stacked + 1;
        }
        ints = 0;
        floats = 0;
        for k in 0..in.argCount {
            t: Temp = p.args.get(in.firstArg + k);
            src: str = "";
            if (staged) { src = self.argSlot(k); } else { src = self.place(t); }
            if (floatClass(p.kindOf(t), p.structOf(t)) > 0) {
                if (floats < FLOAT_ARG_REGS) {
                    self.put("movq xmm");
                    self.putNum(floats);
                    self.put(", ");
                    self.putLine(src);
                    floats = floats + 1;
                }
                continue;
            }
            if (ints >= INT_ARG_REGS) { continue; }
            self.put("mov ");
            self.put(regName(ints));
            self.put(", ");
            self.putLine(src);
            ints = ints + 1;
        }
        return bytes;
    }

    // After a call that passed arguments on the stack: they are the caller's to drop.
    dropStackArgs &self bytes:long -> void {
        if (bytes == 0) { return; }
        self.put("add rsp, ");
        self.putNum(bytes);
        self.putLine("");
    }

    // A temp into an arbitrary memory operand, bouncing through the scratch when the temp is
    // itself in a slot -- x86 has no memory-to-memory move.
    moveToSlot &self dst:str t:Temp -> void {
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
    emitAsmBlock &self p:IRProgram in:Instr -> void {
        self.emitAsmInputs(p, in);
        // The programmer's assembly, verbatim except for `{reg}` placeholders, which render as
        // the sub-register sized to whatever `in`/`out` bound to that register.
        for k in 0..in.pieceCount {
            at: long = in.firstPiece + k;
            if (p.asmKinds.get(at) == AsmKind.Text) {
                self.putLine(self.resolveAsmRegs(p, in, nameOf(p.asmText.get(at))));
            }
        }
        for k in 0..in.pieceCount {
            at: long = in.firstPiece + k;
            if (p.asmKinds.get(at) == AsmKind.Out) {
                self.put("mov ");
                self.put(self.slotOf(p.asmNames.get(at)));
                self.put(", ");
                self.putLine(nameOf(p.asmRegs.get(at)));
            }
        }
    }

    // Each input into the register the block asked for. Not simply in the order written: a value
    // may be sitting in a register another input wants, and moving that one first destroys it.
    // `memcpy`'s `in rdi dst; in rsi src; in rcx n` was exactly that -- `n` was in rdi, so `rdi`
    // was loaded with `dst` before `rcx` read it, and every buffered write copied a pointer's
    // worth of bytes. So a move is emitted only once nothing still pending reads its target, and
    // a cycle is broken by parking the target's current value in the scratch register, which the
    // block already counts as clobbered.
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
            // Every remaining move is blocked by another, so they form a cycle of registers.
            // One is closed with `xchg`: move `k` reads a register another pending move targets,
            // and swapping the two puts k's value in place while the target's old value moves to
            // where k's was, so whoever read either register reads the other instead. No third
            // register is borrowed: parking a value in the scratch (`rax`) clobbered the block's
            // own `in rax` when that had already been loaded (STDLIB_REVIEW gap 1).
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

    // A pending move whose source is a register another pending move writes: in a deadlock every
    // move's target is read by some other, so following those reads ends in a cycle, and any move
    // on it is one.
    cycleMove &self want:Vec<str> have:Vec<str> done:Vec<bool> -> long {
        for k in 0..want.len() {
            if (!done.get(k)) {
                for j in 0..want.len() {
                    if (j != k && !done.get(j) && want.get(j) == have.get(k)) { return k; }
                }
            }
        }
        failStr(stringOf("internal: an asm block's inputs are blocked with no cycle among them"));
        return 0;
    }

    // Does a move still to be made read the register that move `k` is about to overwrite?
    readsLater &self want:Vec<str> have:Vec<str> done:Vec<bool> k:long -> bool {
        for j in 0..want.len() {
            if (j != k && !done.get(j) && have.get(j) == want.get(k)) { return true; }
        }
        return false;
    }

    // `{rax}` in an asm line becomes the sub-register of the width bound to `rax` by this
    // block's `in`/`out`. A placeholder naming a register the block never bound is refused
    // rather than emitted: NASM would read `{rax}` as a decorator and report something that
    // points nowhere near the line the programmer wrote.
    resolveAsmRegs &self p:IRProgram in:Instr line:str -> str {
        out: String;
        i: long = 0;
        while (i < line.len) {
            c: long = charAt(line, i);
            if (c != '{') { out.push(c as char); i = i + 1; }
            else {
                close: long = i + 1;
                while (close < line.len && charAt(line, close) != '}') { close = close + 1; }
                if (close >= line.len) { failStr(format("asm: unclosed register placeholder in: {}", line)); }
                want: str = strSlice(line, i + 1, close - i - 1);
                out.pushStr(self.sizedReg(p, in, want, line));
                i = close + 1;
            }
        }
        held: str = "";
        held = keepString(out);
        return held;
    }
    // The width `in`/`out` bound to `want`, as a register name.
    sizedReg &self p:IRProgram in:Instr want:str line:str -> str {
        for k in 0..in.pieceCount {
            at: long = in.firstPiece + k;
            // An `in` carries the width of the value bound to it; an `out` writes a whole slot,
            // which this port has not narrowed yet, so only an input decides the sub-register.
            if (p.asmKinds.get(at) == AsmKind.In && nameOf(p.asmRegs.get(at)) == want) {
                return regNameSized(regIndexOf(want), p.asmSizes.get(at));
            }
        }
        failStr(format("asm: no in/out binds the register {} used as a placeholder in: {}", want, line));
        return want;
    }

    // A block copy, eight bytes at a time. Every aggregate here is built of 8-byte words and its
    // size is rounded up to one, so there is no tail to handle. Past `UNROLL_COPY_BYTES`, `rep movsq`:
    // two instructions a word was most of what a large struct's copy cost in code.
    emitBlockCopy &self in:Instr -> void {
        if (in.imm > UNROLL_COPY_BYTES) {
            self.forceInto(in.a, SCRATCH);
            self.forceInto(in.b, SCRATCH2);
            self.repMovs(in.imm);
            return;
        }
        // A word at a time through `xmm15`, which nothing else holds between two instructions
        // (floats live in the general registers, and the `xmm` argument registers are filled only
        // at a call), so the two addresses are read where the allocator put them. Eight bytes,
        // not sixteen: what is copied was usually just stored a word at a time (a struct being
        // built), and a 16-byte load across two 8-byte stores cannot be forwarded from them: it
        // waits for both to reach the cache, which measured slower than twice the moves.
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
        r: str = self.rightOperand(in, SCRATCH2);
        self.put("cmp ");
        self.put(l);
        self.put(", ");
        self.putLine(r);
        self.put("set");
        self.put(setSuffix(in.op, typeInfo(in.kind).unsignedNum));
        self.putLine(" al");
        self.putLine("movzx eax, al");
        self.put("mov ");
        self.put(self.place(in.dst));
        self.putLine(", rax");
    }

    // ─── floats ──────────────────────────────────────────────────────────────
    //
    // A float lives where an integer would, as its bits: an `f64`'s 64, an `f32`'s 32 sign-extended
    // (the canonical form of any 4-byte signed value). The allocator has one register class, so an
    // operation moves its operands into `xmm0`/`xmm1`, computes there, and moves the result back.
    // A float the allocator could keep in `xmm8`-`xmm14` lives there (`RegAlloc.markXmm` says
    // which: every instruction touching it is one of the float paths below, each of which reads
    // an operand from an `xmm` register, a general one or a slot). Otherwise it is its bits in a
    // general register, and an operation moves it into `xmm0`/`xmm1` and back. Arguments and
    // results pass in `xmm0`-`xmm7` (`emitArgs`, the prologue, `Ret`).

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
            self.putLine("movsxd rax, eax");
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
        l: str = self.intoScratch(in.a, SCRATCH);
        r: str = self.rightOperand(in, SCRATCH2);
        // Straight into the destination register where there is one and it holds nothing this
        // instruction has still to read: two instructions rather than three, and one when the
        // left operand is already sitting there, which after promotion is the common shape of
        // `i = i + 1`. Both operands are materialised above, before anything writes the
        // destination, and `rax`/`rdx` are never allocated to a temp, so the only value that
        // could be destroyed by writing it is the right operand's own.
        d: long = self.ra.regOf(in.dst);
        if (d != SPILLED && (in.bIsImm || self.ra.regOf(in.b) != d)) {
            dn: str = regName64(d);
            if (!(dn == l)) {
                self.put("mov ");
                self.put(dn);
                self.put(", ");
                self.putLine(l);
            }
            self.put(mnemonic(in.op));
            self.put(" ");
            self.put(dn);
            self.put(", ");
            self.putLine(r);
            self.canonicalize(d, in.kind);
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

    // A variable shift count lives in `cl` and nowhere else: x86 has no `shl r64, r64`. `rcx` is
    // allocatable, so whatever was living there is put back: writing over it lost the temp the
    // allocator had placed in it, silently and only when a shift happened to be near one.
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
            self.put("mov rcx, ");
            self.putLine(self.place(in.b));
            self.put(mn);
            self.putLine(" rax, cl");
            self.putLine("pop rcx");
        }
        self.canonicalize(SCRATCH, in.kind);
        self.put("mov ");
        self.put(self.place(in.dst));
        self.putLine(", rax");
    }

    // `idiv` divides the sign-extended rdx:rax pair, so the dividend goes in rax with rdx holding
    // its sign, `cqo` for a signed operand, a zeroed rdx for an unsigned one, which is a
    // different instruction and a different answer once the top bit is set.
    //
    // The divisor is read where it already is. Routing it through rcx wrote over whatever the
    // allocator had put there, and `'0' + (-(n % 10))` (whose zero was living in rcx) printed
    // every digit ten too high.
    emitDivide &self in:Instr -> void {
        if (in.bIsImm) { self.emitDivideConst(in); return; }
        unsigned: bool = typeInfo(in.kind).unsignedNum;
        l: str = self.intoScratch(in.a, SCRATCH);
        self.put("mov rax, ");
        self.putLine(l);
        if (unsigned) { self.putLine("xor edx, edx"); } else { self.putLine("cqo"); }
        if (unsigned) { self.put("div "); } else { self.put("idiv "); }
        r: long = self.ra.regOf(in.b);
        if (r != SPILLED) { self.putLine(regName64(r)); }
        else {
            self.put("qword ");
            self.putLine(self.place(in.b));
        }
        // The quotient is in rax and the remainder in rdx, and either may need re-extending: a
        // narrow signed division wraps at its own width.
        res: long = SCRATCH;
        if (in.op == IROp.Mod) { res = SCRATCH2; }
        self.canonicalize(res, in.kind);
        self.put("mov ");
        self.put(self.place(in.dst));
        self.put(", ");
        self.putLine(regName64(res));
    }

    // A division or remainder by a constant `d` (`flow.k` puts it on the instruction only for
    // 2 <= d <= 2^31 - 1) without `idiv`: a power of two as shifts, anything else as the high half
    // of `x * M` shifted, M the scaled reciprocal (Granlund and Montgomery; the multiplier as
    // Hacker's Delight 10-1 and 10-2 compute it, `divMagic`). Exact for every 64-bit dividend; a
    // narrower one is its canonical 64-bit word, whose quotient and remainder are the narrow ones
    // (no constant divisor here can overflow), so one sequence serves every width. The quotient
    // ends in rdx; a remainder is then `x - q * d`, in rax. Only rax and rdx are written, as `idiv`
    // writes them, and `x` is read where it lives.
    emitDivideConst &self in:Instr -> void {
        d: long = in.bImm;
        unsigned: bool = typeInfo(in.kind).unsignedNum;
        isMod: bool = in.op == IROp.Mod;
        x: str = self.place(in.a);
        spilled: bool = self.ra.regOf(in.a) == SPILLED;
        res: long = SCRATCH2;
        k: long = exactLog2(d);
        if (k >= 1) {
            self.put("mov rdx, ");
            self.putLine(x);
            if (unsigned) {
                if (isMod) { self.put("and rdx, "); self.putNum(d - 1); }
                else { self.put("shr rdx, "); self.putNum(k); }
                self.putLine("");
            } else {
                // Rounded toward zero: a negative x is biased by d - 1 first.
                self.putLine("sar rdx, 63");
                self.put("shr rdx, ");
                self.putNum(64 - k);
                self.putLine("");
                self.put("add rdx, ");
                self.putLine(x);
                if (isMod) {
                    self.put("and rdx, ");
                    self.putNum(0 - d);
                    self.putLine("");
                    self.put("mov rax, ");
                    self.putLine(x);
                    self.putLine("sub rax, rdx");
                    res = SCRATCH;
                } else {
                    self.put("sar rdx, ");
                    self.putNum(k);
                    self.putLine("");
                }
            }
        } else {
            mg: DivMagic = divMagic(d, unsigned);
            self.put("mov rax, ");
            self.putNum(mg.m);
            self.putLine("");
            if (unsigned) { self.put("mul "); } else { self.put("imul "); }
            if (spilled) { self.put("qword "); }
            self.putLine(x);
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
                // Toward zero: one more for a negative x.
                self.put("mov rax, ");
                self.putLine(x);
                self.putLine("shr rax, 63");
                self.putLine("add rdx, rax");
            }
            if (isMod) {
                self.put("imul rdx, rdx, ");
                self.putNum(d);
                self.putLine("");
                self.put("mov rax, ");
                self.putLine(x);
                self.putLine("sub rax, rdx");
                res = SCRATCH;
            }
        }
        self.canonicalize(res, in.kind);
        self.put("mov ");
        self.put(self.place(in.dst));
        self.put(", ");
        self.putLine(regName64(res));
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

// k when v is 2^k (k >= 1), else -1.
local exactLog2 v:long -> long {
    if (v < 2 || (v & (v - 1)) != 0) { return -1; }
    k: long = 0;
    while ((1 << k) != v) { k = k + 1; }
    return k;
}

// How many floats pass in `xmm` registers, and how many other arguments in general ones (this
// compiler's order: `rax`, `rbx`, `rcx`, `rdx`, `rdi`, `rsi`, `r8`-`r11`, every caller-saved register);
// what is past either goes on the stack.
pub FLOAT_ARG_REGS: long = 8;
pub INT_ARG_REGS: long = 10;

// Whether a value of this type passes as a float (1 an `f64`, 2 an `f32`) or not (0): a backed
// enum or distinct type by what it is stored as, a borrow of a float scalar as the float.
pub floatClass k0:Lit s:Sym -> long {
    k: Lit = k0;
    if (k == Lit.Struct && s != NO_SYM && namedScalar(k, s)) { k = namedScalarBacking(s); }
    if (k == Lit.Ref && s != NO_SYM && namesScalar(nameOf(s))) { k = scalarNamed(nameOf(s)); }
    if (k == Lit.Double) { return 1; }
    if (k == Lit.Float) { return 2; }
    return 0;
}

// ─── names ───────────────────────────────────────────────────────────────────

// Whether this name was declared in this compilation unit and defined in another one.
pub isDeclaredExtern p:IRProgram n:Sym -> bool {
    for i in 0..p.externs.len() {
        if (p.externs.get(i) == n) { return true; }
    }
    return false;
}

// A user function's symbol. `::` becomes `$` so the label is a legal NASM identifier and can
// never collide with an instruction name.
// A function marked `@init` or `@fini`.
pub isHook n:Sym -> bool {
    for k in 0..gInitHooks.len() { if (gInitHooks.get(k) == n) { return true; } }
    for k in 0..gFiniHooks.len() { if (gFiniHooks.get(k) == n) { return true; } }
    return false;
}

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

// How many bytes a value of this type occupies in memory. A slot is always eight, but the memory
// a pointer names is the real thing: an array element, a struct field, a byte in a buffer.
pub widthOf k:Lit -> long {
    w: long = typeInfo(k).size;
    if (w < 1 || w > 8) { return 8; }
    if (w == 3) { return 4; }
    if (w > 4) { return 8; }
    return w;
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

// The wordings a failed check prints, by the label that holds them. One place, so the `mov rdx`
// that sizes each write takes its length from the text itself rather than from a hand count.
pub boundsText label:str -> str {
    if (label == "__methBndHead") { return "panic: index out of range: "; }
    if (label == "__methBndMid")  { return " not in 0..length "; }
    if (label == "__methRngHead") { return "panic: slice bound out of range: "; }
    if (label == "__methBndAt")   { return " at "; }
    return " exceeds ";
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
// the index registers, the rest `r8`-`r15`), so nothing in it says out loud that index 4 is `rdi`.
// The allocator's caller- and callee-saved sets are written as those indices. This runs when the
// compiler is compiled and stops the fold if the two ever stop describing the same registers, so
// only the boundaries the classification actually turns on are worth asserting.
local gRegNumberingChecked: bool = checkRegNumbering();

local checkRegNumbering -> bool {
    if (!strEq(regName64(REG_RAX), "rax")) { panic("register numbering: SCRATCH is not rax"); }
    if (!strEq(regName64(REG_RDX), "rdx")) { panic("register numbering: SCRATCH2 is not rdx"); }
    if (!strEq(regName64(REG_RBX), "rbx")) { panic("register numbering: caller-saved does not start at rbx"); }
    if (!strEq(regName64(REG_R12), "r12")) { panic("register numbering: callee-saved does not start at r12"); }
    if (!strEq(regName64(REG_R15), "r15")) { panic("register numbering: callee-saved does not end at r15"); }
    if (REG_R15 + 1 != REG_COUNT) { panic("REG_COUNT does not match the register numbering"); }
    return true;
}

// The index a 64-bit register name stands for: the inverse of `regName64`, for the one place a
// register arrives as text: an `asm` block's `in`/`out`.
pub regIndexOf name:str -> long {
    hit: Option<long> = gRegIndex.find(name);
    match hit { Some(r) { return r; } None { } }
    failStr(format("asm: unknown register '{}' (use a 64-bit name like rax or rdi)", name));
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
