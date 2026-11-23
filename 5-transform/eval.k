// The compile-time evaluator: an interpreter over the typed tree that runs a piece of the program
// inside the compiler and hands back the value. Every global initializer that can be run is.
//
// The value model is memory exactly as it is at runtime, so the same registry layout offsets read
// it. The segment model and the determinism boundary are in PORT.md; the design is comptime.md.
#include <support::{compiler, fp}>
#include <parse::ast>
#include <parse::parser>     // parseExpr: the compiler's own parser, called from a macro
#include <parse::{registry, types, upstream}>
#include <facts>
#include <stdlib::{chars, fmt, map, option}>
#include <stdlib::path>      // stemOf: the module a file is
#include <stdlib::{mem, string, vec}>

// `--trace-fold`: say, per global, whether it folded and what stopped it if not.
pub var gTraceFold: bool = false;

// How much one fold may spend before it is given up (`--fold-steps=N` and `--fold-heap=MiB`). A
// fold that runs past either limit is refused like any other: an error for a constant, which must
// fold, and a startup initializer for a `var`. The compiler never hangs or exhausts the machine.
pub var gStepLimit: long = 10000000;
pub var gHeapLimit: long = 268435456;    // 256 MiB of compile-time heap

// One compile-time value. `bits` holds a scalar's bits, a pointer's address, or the address of an
// aggregate's storage; `structName` is the companion name the kind needs, as everywhere else.
pub struct CtValue { kind: Lit, structName: Sym, bits: long }

// Appends `n` zero bytes to one of the evaluator's memories with one reservation and one fill.
// Pushing a byte at a time was a cost every frame, local and heap block paid.
local zeroExtend inout v:Vec<u8> n:long -> void {
    if (n <= 0) { return; }
    v.reserve(n);
    unsafe { memset(v.buf.ptr as long + v.count, 0, n); }
    v.count = v.count + n;
}

// Where the literal and heap segments live in the compile-time address space. They sit far above
// anything the stack reaches, so a pointer's value alone says which segment it points into.
local LIT_BASE: long  = 1099511627776;   // 2^40
local HEAP_BASE: long = 2199023255552;   // 2^41

// The Linux x86-64 syscalls and flags the compile-time OS answers (`Evaluator.ctSyscall`).
local SYS_WRITE: long = 1;
local SYS_MMAP: long = 9;
local SYS_MUNMAP: long = 11;
local SYS_MREMAP: long = 25;
local SYS_EXIT: long = 60;
local SYS_EXIT_GROUP: long = 231;
local MAP_FIXED: long = 0x10;
local MAP_ANONYMOUS: long = 0x20;
local MREMAP_MAYMOVE: long = 1;
local MREMAP_FIXED: long = 2;
// A refused syscall's name, for the ones a program is likely to try.
local syscallNote nr:long -> str {
    if (nr == 0) { return " (read)"; }
    if (nr == 2 || nr == 257) { return " (open)"; }
    if (nr == 3) { return " (close)"; }
    if (nr == 39) { return " (getpid)"; }
    if (nr == 56) { return " (clone)"; }
    if (nr == 158) { return " (arch_prctl)"; }
    if (nr == 202) { return " (futex)"; }
    if (nr == 228) { return " (clock_gettime)"; }
    if (nr == 318) { return " (getrandom)"; }
    return "";
}
// A function's address and a vtable's are handles: an index into the program's functions, or
// into the (concrete, trait) pairs this fold made trait objects of. Never dereferenced as memory.
local FN_BASE: long   = 4398046511104;   // 2^42
local VT_BASE: long   = 8796093022208;   // 2^43

// See the effects section at the end of the file.
pub struct Effects {
    all: bool,                    // something opaque was reached: assume every global written
    written: HashMap<str, long>,  // the globals known to be written
    order: Vec<Sym>,              // the same, in the order they were found
    visited: Vec<bool>,           // per function (by its index in `fns`): already merged in
    fnAt: HashMap<long, long>      // resolved name -> `fns` index
}

// A block the compile-time heap handed out, and what became of it.
pub struct CtBlock { start: long, size: long, live: bool, image: long }

pub struct Evaluator {
    fnAt: HashMap<long, long>,   // every function body in the program, by its resolved name
    // What `fnAt` was built from, so it is rebuilt when the page changes and not before.
    indexedPage: long,
    indexedLen: long,
    mem: Vec<u8>,               // the compile-time stack: globals, then frames
    lits: Vec<u8>,              // string literal bytes, addressed from LIT_BASE
    litAt: HashMap<str, long>,  // a literal's spelling -> its index below
    litText: Vec<Sym>,          // the spelling of each, for relocation
    litStart: Vec<long>,        // where each begins in `lits`
    litLens: Vec<long>,         // and its byte length: an empty literal begins where the next does
    heap: Vec<u8>,              // what malloc handed out, addressed from HEAP_BASE
    blocks: Vec<CtBlock>,       // in address order: a bump allocator never reuses
    lastBlock: long,            // the block the last heap access fell in (`inBounds`), or -1
    offsets: HashMap<long, long>, // (a base type, a field) -> its offset, for one evaluation (`fieldOffset`)
    // The globals segment is [0, globalsEnd): read-only to the program (except while `foldInit`
    // commits a folded result into it), and what promotion reads at the end.
    globalAddr: HashMap<str, long>,
    globalsEnd: long,
    committing: bool,
    gNames: Vec<Sym>,           // the globals in address order, for naming a pointer into one
    gStarts: Vec<long>,
    gDecls: Vec<long>,          // each one's `decls` index
    folded: Vec<bool>,          // which of them folded, to be promoted at the end
    // Trait objects made during this fold: handle VT_BASE + i names (concrete, trait).
    vtConcrete: Vec<Sym>,
    vtTrait: Vec<Sym>,
    // The locals of every open frame, innermost last. A call pushes a frame; a block does not get
    // one, because the parser already gave every shadowing declaration a name of its own.
    names: Vec<Sym>,
    slots: Vec<long>,           // where each local's storage is
    kinds: Vec<Lit>,            // what it holds: the element type, for an array
    snames: Vec<Sym>,
    arrays: Vec<bool>,
    counts: Vec<long>,
    // Which locals stand where another value lies rather than in their own slot (`forElement`,
    // `bindBorrow`): a borrow the ownership pass has not made yet.
    aliased: Vec<bool>,
    frameBase: Vec<long>,       // where each frame's locals begin in the lists above
    frameSp: Vec<long>,         // and where its memory began
    // A runaway loop at compile time would hang the compiler, so the steps are counted, and
    // running out of them is a refusal rather than a crash.
    steps: long,
    stopped: bool,
    refusal: String,            // why the last evaluation stopped; empty when it did not
    refused: bool,              // whether it stopped by its own choice, an exit (`ctExit`)
    // What compile-time code wrote to stderr (fd 2) through the `syscall` builtin. If the code
    // then exits (`ctExit`), this is the error's text, as it would have been its last words.
    ctErr: String,
    // Control leaving a statement: a `return` unwinds to the call that made the frame, a
    // `break` or `continue` to the loop around it, each carried as a flag the walk reads.
    returning: bool,
    breaking: bool,
    continuing: bool,
    retVal: CtValue,
    // The image being built by promotion, and the heap blocks it found pointers to. Those are
    // promoted after it, each into an image of its own and only once, however many pointers
    // reach it.
    curBytes: Vec<u8>,
    curOff: Vec<long>,
    curKind: Vec<RelocKind>,
    curTarget: Vec<Sym>,
    curImage: Vec<long>,
    curDelta: Vec<long>,
    queueBlock: Vec<long>,      // block index, and the element type its pointer said it holds
    queueKind: Vec<Lit>,
    queueName: Vec<Sym>,
    // Splicing a macro's Node result: `stdlib::ast`'s Node type, the fresh names this splice gave
    // the declarations in it, and a counter that keeps one splice's names apart from the next's.
    nodeSym: Sym,
    renames: HashMap<str, Sym>,
    macroSeq: long,
    macroRun: bool,             // a macro is running: the globals are a snapshot, writable
    macroFile: Sym,             // where the macro call was written: what `parseExpr` reads names in
    macroPkg: Sym,
    // The globals that an earlier initializer still going to run at startup may write, and so
    // cannot be trusted at compile time. Grown by `foldGlobals` as it meets each one that did
    // not fold, from the effects of everything that initializer can reach.
    poison: Effects,
    // A dependency's globals, loaded from its facts into this run's storage on first read, and
    // its heap blocks, each loaded once: by image index into the facts, -1 until it is.
    extReady: HashMap<str, bool>,
    extBlocks: Vec<long>,
    // The globals segment every macro run starts from (`beginMacro`), as built for the page it was
    // built for: a run starts from a copy of it rather than laying every global of the program out
    // again. A different page, or a page that has grown, builds it anew; `foldGlobals` drops it.
    macroImage: Vec<u8>,
    macroFolded: Vec<bool>,
    macroPage: long,
    macroPageLen: long,
    // The statement `execBlock` is running, for a store that asks what follows it (`bindBorrow`),
    // and per such store whether what follows may write through what it binds (`mayWriteAfter`).
    curBlock: long,
    curAt: long,
    writeAfter: HashMap<long, bool>
}

methods Evaluator for Default {
    new -> Evaluator {
        r: String; ps: Effects; ce: String;
        return Evaluator { fnAt: map![], indexedPage: -1, indexedLen: -1, mem: vec![], lits: vec![], litAt: map![], litText: vec![], litStart: vec![], litLens: vec![],
                           heap: vec![], blocks: vec![], lastBlock: -1, offsets: map![], globalAddr: map![], globalsEnd: 0, committing: false,
                           gNames: vec![], gStarts: vec![], gDecls: vec![], folded: vec![], vtConcrete: vec![], vtTrait: vec![],
                           names: vec![], slots: vec![], kinds: vec![], snames: vec![], arrays: vec![], counts: vec![], aliased: vec![],
                           frameBase: vec![], frameSp: vec![], steps: 0, stopped: false, refusal: r, refused: false, ctErr: ce,
                           returning: false, breaking: false, continuing: false,
                           retVal: CtValue { kind: Lit.Void, structName: NO_SYM, bits: 0 },
                           curBytes: vec![], curOff: vec![], curKind: vec![], curTarget: vec![], curImage: vec![], curDelta: vec![],
                           queueBlock: vec![], queueKind: vec![], queueName: vec![],
                           nodeSym: NO_SYM, renames: map![], macroSeq: 0, macroRun: false, macroFile: NO_SYM, macroPkg: NO_SYM, poison: ps, extReady: map![], extBlocks: vec![],
                           macroImage: vec![], macroFolded: vec![], macroPage: -1, macroPageLen: -1,
                           curBlock: -1, curAt: 0, writeAfter: map![] };
    }
}

// ─── the entry point ─────────────────────────────────────────────────────────

methods Evaluator {
    // Tries every file global's initializer in declaration order, then promotes what folded.
    // Returns how many folded.
    //
    // Every global gets its storage first, so an initializer that reads one already folded finds
    // its bytes exactly where a later initializer would at runtime. Promotion waits until the end
    // because a later initializer may write through a pointer into a heap block an earlier global
    // owns, and the image must show the final state. That is the state the runtime order would
    // have produced: a folded initializer reaches a block only through a global no startup code
    // writes, and all such initializers are folded in declaration order.
    foldGlobals &self inout a:Ast page:long -> long {
        self.indexFunctions(a, page);
        self.poison.reset(a);
        // What a dependency's startup initializers may write: they run before this package's,
        // whether or not the module declaring one is included here.
        if (gFacts.poisonAll) { self.poison.all = true; }
        for pz in gFacts.poison { self.poison.mark(pz); }
        self.macroRun = false;
        self.macroPage = -1;            // the macros' snapshot is laid out over what this clears
        self.mem.clear();
        self.extReady.clear();
        self.alloc(16);                 // address 0 is null, and belongs to nothing
        self.globalAddr.clear();
        self.gNames.clear(); self.gStarts.clear(); self.gDecls.clear(); self.folded.clear();
        n: long = a.blockLen(page);
        gpos: Vec<long>;                 // each global's position, for what folding it says
        for k in 0..n {
            st: Stmt = a.stmtAt(page, k);
            if (st.kind == StmtKind.VarDecl) {
                d: VarDeclNode = a.decls.get(st.at);
                addr: long = self.alloc(declaredBytesOf(d));
                self.globalAddr.put(nameOf(d.name), addr);
                self.gNames.push(d.name); self.gStarts.push(addr); self.gDecls.push(st.at);
                gpos.push(a.stmtPos.get(a.stmtIdAt(page, k)));
                self.folded.push(false);
            }
        }
        self.globalsEnd = self.mem.len();
        count: long = 0;
        for g in 0..self.gDecls.len() {
            d: VarDeclNode = a.decls.get(self.gDecls.get(g));
            gPos = gpos.get(g);
            // A dependency's global was folded (or not) where it was compiled; its value is read
            // from that package's facts when something here reads it.
            if (d.init != NO_NODE && !isExternGlobal(d.name)) {
                if (self.foldInit(a, d, self.gStarts.get(g))) { self.folded.set(g, true); count = count + 1; }
                else {
                    if (gTraceFold) { eprintln("fold {}: met {}", nameOf(d.name), self.refusal); }
                    // A `const` is a promise that this is computed here; a refusal is then an
                    // error, and it says what stopped the computation.
                    if (!isVarGlobal(d.name)) {
                        failStr(format("`{}` cannot be computed at compile time: it met {}\nnote: a global is a constant unless it is declared `var`\nhelp: declare it `var {}: ...` to initialize it at startup instead", lastComponentOf(nameOf(d.name)), self.refusal, lastComponentOf(nameOf(d.name))));
                    }
                    self.poison.addExpr(a, d.init);
                }
            }
        }
        gPos = 0;
        self.promoteAll(a);
        return count;
    }

    // Runs one initializer into the global's own storage. An initializer that is already a
    // literal only needs its bytes put there.
    foldInit &self inout a:Ast d:VarDeclNode addr:long -> bool {
        e: Expr = a.expr(d.init);
        if (e.op == Op.Literal && !d.isArray && ctScalar(d.kind, d.structName)) {
            self.committing = true;
            self.storeLiteral(addr, d, e);
            self.committing = false;
            return true;
        }
        if (e.op == Op.Image) { return true; }
        self.reset();
        v: CtValue = self.eval(a, d.init);
        if (self.stopped) { return false; }
        self.committing = true;
        if (d.isArray) { self.copy(addr, self.arrayFrom(a, d.init, v), declaredBytesOf(d)); }
        else { self.assignTo(addr, d.kind, d.structName, v); }
        self.committing = false;
        return !self.stopped;
    }

    // Writes a global's literal initializer into its storage: an integer's value, or a float
    // literal's spelling rounded once at the global's width. A float literal arrives as text, so
    // without the second case `G: f64 = 3.5` would start out as 0.0.
    storeLiteral &self addr:long d:VarDeclNode e:Expr -> void {
        match e.payload {
            Num(v) { self.store(addr, d.kind, d.structName, v); }
            Text(t) {
                sk: Lit = storedKind(d.kind, d.structName);
                if (isFloat(sk)) { self.store(addr, d.kind, d.structName, decimalToFloat(nameOf(t), sk == Lit.Float)); }
            }
            _ { }
        }
    }

    // ─── promotion: a value's bytes, with its pointers named ─────────────────
    //
    // Promotion walks each folded global by its layout rather than copying raw bytes, because
    // only the type can say whether a word is a pointer. A `str` becomes a relocation to its
    // literal's label. A pointer into the heap names the block it reaches, which is then promoted
    // as an image of its own, once however many pointers reach it, so a shared block stays
    // shared. A pointer into a global names that global, and a function or a vtable names its
    // label. An address held in a plain integer, or one into the compile-time stack, has no
    // `.data` counterpart; it is refused, and that global initializes at startup after all.
    promoteAll &self inout a:Ast -> void {
        for g in 0..self.gDecls.len() {
            if (self.folded.get(g)) {
                d: VarDeclNode = a.decls.get(self.gDecls.get(g));
                if (!self.promoteGlobal(a, d, self.gStarts.get(g))) {
                    if (gTraceFold) { eprintln("promote {}: met {}", nameOf(d.name), self.refusal); }
                    if (!isVarGlobal(d.name)) { failStr(format("`{}` cannot be placed in the binary: it met {}\nhelp: declare it `var {}: ...` to build it at startup instead", lastComponentOf(nameOf(d.name)), self.refusal, lastComponentOf(nameOf(d.name)))); }
                    self.folded.set(g, false);
                } else if (gTraceFold) { eprintln("fold {}: in .data", nameOf(d.name)); }
            }
        }
    }

    promoteGlobal &self inout a:Ast d:VarDeclNode addr:long -> bool {
        e: Expr = a.expr(d.init);
        if (e.op == Op.Image) { return true; }
        if (!d.isArray && ctScalar(d.kind, d.structName)) {
            v: long = self.load(addr, d.kind, d.structName);
            a.setExpr(d.init, Expr { op: Op.Literal, left: NO_NODE, right: NO_NODE, kind: d.kind,
                                     structName: NO_SYM, isParen: false, payload: Payload.Num(v) });
            return true;
        }
        self.stopped = false;
        self.refusal.clear();
        mark: long = a.images.len();      // the blocks this promotion reaches get images past here
        self.beginImage();
        if (d.isArray) {
            w: long = typeBytes(d.kind, d.structName);
            i: long = 0;
            while (i < d.count && !self.stopped) { self.imageOf(a, addr + i * w, d.kind, d.structName); i = i + 1; }
        } else {
            self.imageOf(a, addr, d.kind, d.structName);
        }
        if (self.stopped) { self.abandon(a, mark); return false; }
        idx: long = self.finishImage(a, false);
        self.promoteQueued(a);
        if (self.stopped) { self.abandon(a, mark); return false; }
        a.setExpr(d.init, Expr { op: Op.Image, left: NO_NODE, right: NO_NODE, kind: e.kind,
                                 structName: e.structName, isParen: false, payload: Payload.Image(idx) });
        return true;
    }

    // Promotes the blocks the last image reached, each into an image of its own; walking a block
    // may reach more. Each was given its image index when it was first reached, so a pointer to a
    // block already promoted, or still being promoted in a cycle, names the same label.
    promoteQueued &self inout a:Ast -> void {
        while (self.queueBlock.len() > 0 && !self.stopped) {
            b: long = self.queueBlock.pop();
            k: Lit = self.queueKind.pop();
            n: Sym = self.queueName.pop();
            blk: CtBlock = self.blocks.get(b);
            self.beginImage();
            w: long = typeBytes(k, n);
            if (w < 1) { w = 1; }
            i: long = 0;
            while (i + w <= blk.size && !self.stopped) { self.imageOf(a, blk.start + i, k, n); i = i + w; }
            while (i < blk.size) { self.curBytes.push(self.rawByte(blk.start + i)); i = i + 1; }
            if (self.stopped) { self.discardImage(); return; }
            self.finishImageAt(a, blk.image);
        }
    }

    // A promotion that failed: every block it gave an image to is unpromoted again, so a later
    // global reaching one walks it afresh, and the images it made are left empty and unlabeled.
    abandon &self inout a:Ast mark:long -> void {
        self.discardImage();
        for b in 0..self.blocks.len() {
            blk: CtBlock = self.blocks.get(b);
            if (blk.image >= mark) { blk.image = -1; self.blocks.set(b, blk); }
        }
        for i in mark..a.images.len() {
            im: ImageNode = a.images.get(i);
            a.images.set(i, ImageNode { firstByte: im.firstByte, byteCount: 0, firstReloc: im.firstReloc, relocCount: 0, isBlock: false });
        }
    }
    beginImage &self -> void {
        self.curBytes.clear(); self.curOff.clear(); self.curKind.clear();
        self.curTarget.clear(); self.curImage.clear(); self.curDelta.clear();
    }
    discardImage &self -> void { self.beginImage(); self.queueBlock.clear(); self.queueKind.clear(); self.queueName.clear(); }
    // Append the image being built as a run and give it a node; `isBlock` says whether it needs a
    // label of its own in `.data`.
    finishImage &self inout a:Ast isBlock:bool -> long {
        a.images.push(ImageNode { firstByte: 0, byteCount: 0, firstReloc: 0, relocCount: 0, isBlock: isBlock });
        idx: long = a.images.len() - 1;
        self.finishImageAt(a, idx);
        return idx;
    }
    finishImageAt &self inout a:Ast idx:long -> void {
        firstByte: long = a.imageBytes.len();
        a.imageBytes.extend(self.curBytes);
        firstReloc: long = a.relocs.len();
        for r in 0..self.curOff.len() {
            a.relocs.push(RelocNode { offset: self.curOff.get(r), kind: self.curKind.get(r),
                                      target: self.curTarget.get(r), image: self.curImage.get(r),
                                      delta: self.curDelta.get(r) });
        }
        was: ImageNode = a.images.get(idx);
        a.images.set(idx, ImageNode { firstByte: firstByte, byteCount: self.curBytes.len(),
                                      firstReloc: firstReloc, relocCount: self.curOff.len(),
                                      isBlock: was.isBlock });
        self.beginImage();
    }
    reloc &self kind:RelocKind target:Sym image:long delta:long -> void {
        self.curOff.push(self.curBytes.len());
        self.curKind.push(kind);
        self.curTarget.push(target);
        self.curImage.push(image);
        self.curDelta.push(delta);
    }

    // One value's bytes into the image being built, its pointer words named.
    imageOf &self inout a:Ast addr:long kind:Lit sname:Sym -> void {
        if (self.stopped) { return; }
        k: Lit = storedKind(kind, sname);
        if (isInteger(k) || k == Lit.Bool) {
            w: long = typeInfo(k).size;
            if (w == 8) {
                v: long = self.loadWord(addr);
                if (v >= LIT_BASE && self.addressed(v)) {
                    self.stop(stringOf("an address held in a plain integer, which `.data` cannot relocate")); return;
                }
            }
            self.rawBytes(addr, w);
            return;
        }
        // A float is its bits, which name nothing: an `f64` field, element or payload is copied
        // as it lies, as an integer of its width is.
        if (k == Lit.Double || k == Lit.Float) {
            self.rawBytes(addr, typeInfo(k).size);
            return;
        }
        if (k == Lit.Str || k == Lit.Slice) {
            ek: Lit = Lit.U8;
            en: Sym = NO_SYM;
            if (k == Lit.Slice && sname != NO_SYM) { t: TypeRef = unmangledType(nameOf(sname)); ek = t.base; en = t.name; }
            self.imagePointer(a, addr, ek, en);
            self.rawBytes(addr + 8, 8);
            return;
        }
        if (k == Lit.Ptr || k == Lit.Ref) {
            ek: Lit = Lit.U8;
            en: Sym = NO_SYM;
            if (k == Lit.Ref) { ek = Lit.Struct; en = sname; }
            else if (sname != NO_SYM) { t: TypeRef = unmangledType(nameOf(sname)); ek = t.base; en = t.name; }
            self.imagePointer(a, addr, ek, en);
            return;
        }
        if (k == Lit.Fn) {
            v: long = self.loadWord(addr);
            if (v == 0) { self.rawBytes(addr, 8); return; }
            if (v < FN_BASE || v >= VT_BASE || v - FN_BASE >= a.fns.len()) { self.stop(stringOf("a function value that names no function")); return; }
            self.reloc(RelocKind.Fn, a.fns.get(v - FN_BASE).name, -1, 0);
            self.rawBytes(addr, 8);
            return;
        }
        if (k == Lit.TraitObj) {
            // {data, vtable}: the vtable handle says what concrete type the data is, which is
            // what its block is walked as; the vtable itself is a label the emitter writes.
            h: long = self.loadWord(addr + 8);
            if (h < VT_BASE || h - VT_BASE >= self.vtConcrete.len()) { self.stop(stringOf("a trait object with no vtable")); return; }
            concrete: Sym = self.vtConcrete.get(h - VT_BASE);
            trait: Sym = self.vtTrait.get(h - VT_BASE);
            self.imagePointer(a, addr, Lit.Struct, concrete);
            gReg.ensureImpl(concrete, trait);
            self.reloc(RelocKind.Vtable, intern(vtableName(concrete, trait)), -1, 0);
            noteVtablePair(vtableName(concrete, trait), concrete, trait);
            self.rawBytes(addr + 8, 8);
            return;
        }
        if (k == Lit.Struct || k == Lit.Tuple) {
            si: long = gReg.findStructSym(sname);
            if (si < 0) { self.stop(format("a value of type `{}` it cannot lay out", nameOf(sname))); return; }
            self.imageStruct(a, addr, gReg.structDef(si));
            return;
        }
        self.stop(format("a value of type `{}` it cannot promote", typeName(k)));
    }

    // A struct's fields in offset order, padding as raw bytes. A sum type overlaps its payloads,
    // so only the live variant's are words with a type: the tag says which, and the bytes the
    // other variants would have used come through raw.
    imageStruct &self inout a:Ast addr:long d:StructDef -> void {
        cursor: long = 0;
        first: long = 0;
        count: long = d.fieldCount;
        if (d.isEnum) {
            ei: long = gReg.findEnumSym(d.name);
            if (ei < 0) { self.stop(format("a sum type `{}` it cannot lay out", nameOf(d.name))); return; }
            ed: EnumDef = gReg.enumDef(ei);
            tag: long = self.load(addr, ed.backing, NO_SYM);
            self.rawBytes(addr, typeInfo(ed.backing).size);
            cursor = typeInfo(ed.backing).size;
            first = -1;
            for v in 0..ed.variantCount {
                vd: VariantDef = gReg.variantAt(ed, v);
                if (vd.value == tag) { first = 1 + vd.firstPayload; count = first + vd.payloadCount; }
            }
            if (first < 0) { self.stop(format("a `{}` whose tag {} names no variant", nameOf(d.name), tag)); return; }
        }
        f: long = first;
        while (f < count && !self.stopped) {
            fd: FieldDef = gReg.fieldAt(d, f);
            while (cursor < fd.offset) { self.curBytes.push(self.rawByte(addr + cursor)); cursor = cursor + 1; }
            w: long = typeBytes(fd.kind, fd.structName);
            n: long = 1;
            if (fd.isArray) { n = fd.count; }
            i: long = 0;
            while (i < n && !self.stopped) {
                self.imageOf(a, addr + cursor, fd.kind, fd.structName);
                cursor = cursor + w;
                i = i + 1;
            }
            f = f + 1;
        }
        while (cursor < d.size) { self.curBytes.push(self.rawByte(addr + cursor)); cursor = cursor + 1; }
    }

    // A pointer word holding `elemKind`s: null, or into a segment `.data` can name.
    imagePointer &self inout a:Ast addr:long elemKind:Lit elemName:Sym -> void {
        p: long = self.loadWord(addr);
        if (p == 0) { self.rawBytes(addr, 8); return; }
        if (p >= HEAP_BASE) {
            b: long = self.blockOf(p);
            if (b < 0 || !self.blocks.get(b).live) { self.stop(stringOf("a pointer to freed memory")); return; }
            blk: CtBlock = self.blocks.get(b);
            if (blk.image < 0) {
                // The first time a block is reached it gets its image, so every other pointer to
                // it, including one from inside its own contents, names the same one.
                a.images.push(ImageNode { firstByte: 0, byteCount: 0, firstReloc: 0, relocCount: 0, isBlock: true });
                blk.image = a.images.len() - 1;
                self.blocks.set(b, blk);
                self.queueBlock.push(b); self.queueKind.push(elemKind); self.queueName.push(elemName);
            }
            self.reloc(RelocKind.Block, NO_SYM, self.blocks.get(b).image, p - blk.start);
            self.rawBytes(addr, 8);
            return;
        }
        if (p >= LIT_BASE) {
            li: long = self.litIndexOf(p);
            if (li < 0) { self.stop(stringOf("a pointer past the string literals")); return; }
            self.reloc(RelocKind.Str, self.litText.get(li), -1, p - LIT_BASE - self.litStart.get(li));
            self.rawBytes(addr, 8);
            return;
        }
        if (p < self.globalsEnd) {
            g: long = self.globalOf(p);
            if (g < 0) { self.stop(stringOf("a pointer below the globals")); return; }
            self.reloc(RelocKind.Global, self.gNames.get(g), -1, p - self.gStarts.get(g));
            self.rawBytes(addr, 8);
            return;
        }
        self.stop(stringOf("a pointer into the compile-time stack, which `.data` cannot hold"));
    }
    rawBytes &self addr:long n:long -> void {
        for i in 0..n { self.curBytes.push(self.rawByte(addr + i)); }
    }
    // Whether an integer value is an address in one of the segments, which a plain `long` must
    // not carry into `.data`.
    addressed &self v:long -> bool {
        if (v >= VT_BASE) { return v - VT_BASE < self.vtConcrete.len(); }
        if (v >= FN_BASE) { return true; }
        if (v >= HEAP_BASE) { return self.blockOf(v) >= 0; }
        return v - LIT_BASE < self.lits.len();
    }
    // Which global an address in the globals segment falls in: the last starting at or before it.
    globalOf &self p:long -> long {
        i: long = self.gStarts.len();
        while (i > 0) {
            i = i - 1;
            if (self.gStarts.get(i) <= p) { return i; }
        }
        return -1;
    }
    // Which literal a segment address falls in: the last one starting at or before it.
    litIndexOf &self p:long -> long {
        off: long = p - LIT_BASE;
        if (off < 0 || off > self.lits.len()) { return -1; }
        i: long = self.litStart.len();
        while (i > 0) {
            i = i - 1;
            if (self.litStart.get(i) <= off) { return i; }
        }
        return -1;
    }

    // Every function on the page, by name. Rebuilt only when the page has actually changed.
    //
    // This is called before every macro run, before the globals snapshot each run gets, and once
    // per macro argument. Clearing the table and re-indexing all fifteen hundred functions every
    // time made it the largest single cost in the compiler: a constructor with twenty `vec![]`
    // fields paid for it eighty times, and `Registry_new` took 101 ms, `types::gTypeRows` 169 ms
    // and the stamping rounds 1.2 s between them, almost all of it spent here.
    //
    // The length is enough to tell a changed page from an unchanged one: the page only ever grows
    // (derived definitions are appended), and a macro splice rewrites expressions inside a body
    // rather than the page's own statements.
    indexFunctions &self inout a:Ast page:long -> void {
        n: long = a.blockLen(page);
        if (page == self.indexedPage && n == self.indexedLen) { return; }
        self.fnAt.clear();
        for k in 0..n {
            st: Stmt = a.stmtAt(page, k);
            if (st.kind == StmtKind.FunctionDef) { self.fnAt.put(a.fns.get(st.at).name as long, st.at); }
        }
        self.indexedPage = page;
        self.indexedLen = n;
    }

    // Between two initializers: the frames are gone; the globals, the literals, the heap stay.
    reset &self -> void {
        self.names.clear(); self.slots.clear(); self.kinds.clear(); self.snames.clear();
        self.arrays.clear(); self.counts.clear(); self.aliased.clear();
        self.frameBase.clear();
        self.frameSp.clear();
        self.frameBase.push(0);
        self.frameSp.push(self.mem.len());
        self.steps = 0;
        self.offsets.clear();             // layouts may have settled since (`fieldOffset`)
        self.stopped = false;
        self.refusal.clear();
        self.refused = false;
        self.ctErr.clear();
        self.returning = false;
        self.breaking = false;
        self.continuing = false;
    }

    // ─── the boundary ────────────────────────────────────────────────────────

    stop &self why:String -> CtValue {
        if (!self.stopped) { self.stopped = true; self.refusal = why; }
        return CtValue { kind: Lit.Void, structName: NO_SYM, bits: 0 };
    }
    tick &self -> bool {
        self.steps = self.steps + 1;
        if (self.steps > gStepLimit) {
            self.stop(format("a fold of more than {} steps (`--fold-steps=N` raises the limit)", gStepLimit));
            return false;
        }
        return true;
    }

    // ─── memory ──────────────────────────────────────────────────────────────

    // Fresh zeroed storage on the compile-time stack, word-aligned.
    alloc &self bytes:long -> long {
        n: long = bytes;
        if (n < 1) { n = 1; }
        pad: long = (8 - (self.mem.len() & 7)) & 7;
        zeroExtend(&self.mem, pad);
        addr: long = self.mem.len();
        zeroExtend(&self.mem, n);
        return addr;
    }
    // Hands out a heap block: bump-allocated, 16-aligned, zeroed and never reused, so a stale
    // pointer finds a block marked dead rather than someone else's bytes.
    ctMalloc &self n:long -> long {
        zeroExtend(&self.heap, (16 - (self.heap.len() & 15)) & 15);
        start: long = HEAP_BASE + self.heap.len();
        size: long = n;
        if (size < 1) { size = 1; }
        if (size > gHeapLimit - self.heap.len()) {
            self.stop(format("a compile-time heap past {} MiB (`--fold-heap=MiB` raises the limit)", gHeapLimit / 1048576));
            return start;
        }
        zeroExtend(&self.heap, size);
        self.blocks.push(CtBlock { start: start, size: size, live: true, image: -1 });
        return start;
    }
    ctFree &self p:long -> void {
        if (p == 0) { return; }
        b: long = self.blockOf(p);
        if (b < 0 || self.blocks.get(b).start != p) { self.stop(stringOf("a free of something `malloc` did not hand out")); return; }
        blk: CtBlock = self.blocks.get(b);
        if (!blk.live) { self.stop(stringOf("a block freed twice")); return; }
        blk.live = false;
        self.blocks.set(b, blk);
    }
    // The block an address falls in, or -1. Blocks are in address order, so a binary search.
    blockOf &self p:long -> long {
        lo: long = 0;
        hi: long = self.blocks.len();
        while (lo < hi) {
            mid: long = (lo + hi) / 2;
            if (self.blocks.get(mid).start <= p) { lo = mid + 1; } else { hi = mid; }
        }
        if (lo == 0) { return -1; }
        b: CtBlock = self.blocks.get(lo - 1);
        if (p < b.start + b.size) { return lo - 1; }
        return -1;
    }
    // Whether [addr, addr+n) is readable: on the stack, in a literal, or in a live block.
    inBounds &self addr:long n:long -> bool {
        if (addr >= HEAP_BASE) {
            // Accesses come in runs on one block (a loop over a buffer, a struct's fields), so
            // the last one's block is asked first and the search is the exception.
            b: long = self.lastBlock;
            if (b < 0 || addr < self.blocks.get(b).start || addr >= self.blocks.get(b).start + self.blocks.get(b).size) {
                b = self.blockOf(addr);
                if (b < 0) { return false; }
                self.lastBlock = b;
            }
            blk: CtBlock = self.blocks.get(b);
            return blk.live && addr + n <= blk.start + blk.size;
        }
        if (addr >= LIT_BASE) { return addr - LIT_BASE + n <= self.lits.len(); }
        return addr >= 0 && addr + n <= self.mem.len();
    }
    // Whether a write may land on [addr, addr+n). A global's storage is what the program starts
    // with, so a write to it here would be a startup effect that never happens at runtime once
    // the initializer making it is folded away. It is refused by address rather than by name, so
    // a write through a pointer to a global is refused the same way.
    writable &self addr:long n:long -> bool {
        if (addr >= LIT_BASE && addr < HEAP_BASE) { self.stop(stringOf("a write to a string literal")); return false; }
        if (!self.inBounds(addr, n)) { self.stop(stringOf("a write outside compile-time memory")); return false; }
        if (addr < self.globalsEnd && !self.committing && !self.macroRun) {
            g: long = self.globalOf(addr);
            if (g >= 0) { self.stop(format("a write to the global `{}`", nameOf(self.gNames.get(g)))); }
            else { self.stop(stringOf("a write to a global")); }
            return false;
        }
        return true;
    }
    rawByte &self addr:long -> u8 {
        if (addr >= HEAP_BASE) { return self.heap.get(addr - HEAP_BASE); }
        if (addr >= LIT_BASE) { return self.lits.get(addr - LIT_BASE); }
        return self.mem.get(addr);
    }
    rawSet &self addr:long v:u8 -> void {
        if (addr >= HEAP_BASE) { self.heap.set(addr - HEAP_BASE, v); return; }
        self.mem.set(addr, v);
    }
    byteAt &self addr:long -> long {
        if (!self.inBounds(addr, 1)) { self.stop(format("a read outside compile-time memory (a byte at {})", addr)); return 0; }
        return self.rawByte(addr) as long;
    }
    // Where compile-time address `addr` is in the compiler's own memory: the byte of the stack,
    // the literals or the heap that holds it. Only for a range `inBounds` has passed, and only
    // until that region next grows.
    hostAddr &self addr:long -> long {
        unsafe {
            if (addr >= HEAP_BASE) { return self.heap.buf.ptr as long + (addr - HEAP_BASE); }
            if (addr >= LIT_BASE) { return self.lits.buf.ptr as long + (addr - LIT_BASE); }
            return self.mem.buf.ptr as long + addr;
        }
    }
    loadWord &self addr:long -> long { return self.loadBits(addr, 8); }
    // `w` bytes, little-endian, zero-extended: a word is one load, the rest byte by byte.
    loadBits &self addr:long w:long -> long {
        if (!self.inBounds(addr, w)) { self.stop(format("a read outside compile-time memory ({} bytes at {})", w, addr)); return 0; }
        p: long = self.hostAddr(addr);
        v: long = 0;
        unsafe {
            if (w == 8) { return *(p as *long); }
            i: long = w;
            while (i > 0) { i = i - 1; v = (v << 8) | (*((p + i) as *u8) as long); }
        }
        return v;
    }
    storeBits &self addr:long w:long v:long -> void {
        if (!self.writable(addr, w)) { return; }
        p: long = self.hostAddr(addr);
        unsafe {
            if (w == 8) { *(p as *long) = v; return; }
            x: long = v;
            for i in 0..w { *((p + i) as *u8) = (x & 255) as u8; x = x >> 8; }
        }
    }
    // A scalar of a type, at its stored width, extended the way a load of that type is.
    load &self addr:long kind:Lit sname:Sym -> long {
        k: Lit = storedKind(kind, sname);
        w: long = typeInfo(k).size;
        if (w < 1 || w > 8) { w = 8; }
        return wrapTo(self.loadBits(addr, w), k);
    }
    store &self addr:long kind:Lit sname:Sym v:long -> void {
        k: Lit = storedKind(kind, sname);
        w: long = typeInfo(k).size;
        if (w < 1 || w > 8) { w = 8; }
        self.storeBits(addr, w, v);
    }
    // A block move, safe for overlap: backwards when the destination is above the source.
    copy &self dst:long src:long n:long -> void {
        if (n <= 0) { return; }
        if (!self.inBounds(src, n)) {
            b: long = self.blockOf(src);
            if (b >= 0) {
                blk: CtBlock = self.blocks.get(b);
                self.stop(format("a read outside compile-time memory (a copy of {} bytes from {}: block {} of {} bytes, live {})", n, src, blk.start, blk.size, blk.live));
            } else { self.stop(format("a read outside compile-time memory (a copy of {} bytes from {}: no block)", n, src)); }
            return;
        }
        if (!self.writable(dst, n)) { return; }
        d: long = self.hostAddr(dst);
        s: long = self.hostAddr(src);
        // The regions are separate buffers, so the two ranges overlap only within one of them.
        if (d >= s + n || s >= d + n) { unsafe { memcpy(d, s, n); } return; }
        unsafe {
            if (d > s) {
                i: long = n;
                while (i > 0) { i = i - 1; *((d + i) as *u8) = *((s + i) as *u8); }
                return;
            }
            for at in 0..n { *((d + at) as *u8) = *((s + at) as *u8); }
        }
    }

    // A string literal's bytes, resolved once and shared by every mention of the same spelling.
    // Returns the address of a fresh {ptr, len} pair for it.
    literal &self text:Sym -> long {
        start: long = self.literalStart(text);
        li: long = self.litAt.find(nameOf(text)).unwrapOr(0);
        pair: long = self.alloc(16);
        self.storeBits(pair, 8, start);
        self.storeBits(pair + 8, 8, self.litLens.get(li));
        return pair;
    }
    // The address of a literal's resolved bytes, placing them the first time.
    literalStart &self text:Sym -> long {
        hit: Option<long> = self.litAt.find(nameOf(text));
        li: long = -1;
        match hit { Some(i) { li = i; } None { } }
        if (li < 0) {
            li = self.litStart.len();
            self.litAt.put(nameOf(text), li);
            self.litText.push(text);
            self.litStart.push(self.lits.len());
            s: str = nameOf(text);
            i: long = 0;
            while (i < s.len) {
                c: long = charAt(s, i);
                if (c == 92 && i + 1 < s.len) { i = i + 1; c = escapeByte(charAt(s, i)); }
                self.lits.push(c as u8);
                i = i + 1;
            }
            self.litLens.push(self.lits.len() - self.litStart.get(li));
        }
        return LIT_BASE + self.litStart.get(li);
    }

    // ─── locals ──────────────────────────────────────────────────────────────

    findLocal &self n:Sym -> long {
        base: long = self.frameBase.last();
        // This runs for every variable the evaluator reads or writes, so it walks the names as a
        // slice, where reading an element is a plain load rather than a call to `get`.
        xs: [Sym] = self.names.asSlice();
        i: long = xs.len;
        while (i > base) {
            i = i - 1;
            if (xs[i] == n) { return i; }
        }
        return -1;
    }
    declare &self d:VarDeclNode -> long {
        slot: long = self.alloc(declaredBytesOf(d));
        self.names.push(d.name);
        self.slots.push(slot);
        self.kinds.push(d.kind);
        self.snames.push(d.structName);
        self.arrays.push(d.isArray);
        self.counts.push(d.count);
        self.aliased.push(false);
        return slot;
    }
    pushFrame &self -> void {
        self.frameBase.push(self.names.len());
        self.frameSp.push(self.mem.len());
    }
    popFrame &self -> void {
        base: long = self.frameBase.pop();
        while (self.names.len() > base) {
            self.names.pop(); self.slots.pop(); self.kinds.pop(); self.snames.pop();
            self.arrays.pop(); self.counts.pop(); self.aliased.pop();
        }
        sp: long = self.frameSp.pop();
        self.mem.truncate(sp);
    }

    // Handles `x = $forpK[$foriK]` at the head of a `for x in xs` whose element is a struct. A
    // macro runs during the checker's rounds, before the ownership pass has turned `x` into the
    // borrow it will become (`Checker.bmForLoop`). So instead of copying, `x` is made to stand
    // where the element lies, which is what the borrow means: a write through it in
    // `for x in &xs` reaches the collection. Returns true when this was that statement.
    forElement &self inout a:Ast v:NodeId -> bool {
        e: Expr = a.expr(v);
        if (e.op != Op.Assignment || e.right == NO_NODE) { return false; }
        l: Expr = a.expr(e.left);
        r: Expr = a.expr(e.right);
        if (l.op != Op.Lvalue || l.kind != Lit.Struct || r.op != Op.ArrayIndex
            || namedScalar(l.kind, l.structName)) { return false; }
        ix: long = -1;
        match r.payload { Index(i) { ix = i; } _ { return false; } }
        if (forPointerOf(a, a.indexes.get(ix).base) == NO_SYM) { return false; }
        n: Sym = NO_SYM;
        match l.payload { Name(x) { n = x; } _ { return false; } }
        at: long = self.findLocal(n);
        if (at < 0) { return false; }
        addr: long = self.elemAddress(a, e.right);
        if (self.stopped) { return true; }
        self.slots.set(at, addr);
        self.aliased.set(at, true);
        return true;
    }

    // A match's binding (`p = e.$Pt$0`), a destructured name (`a = $tupN.$0`), or the hidden local
    // a match or a destructure reads its subject into (`$matchN = h.f`, `$bmatchN = x`,
    // `$tupN = self.pair`), stored while a macro runs. Which of these are borrows is decided later
    // (`Checker.borrowMatches`, and the guard's `promoteCopies` for a value that owns nothing), but
    // a binding of a value this frame does not own is the value where it lies wherever the code
    // after it may write through it, and so is a hidden local of such a value. So, as `forElement`
    // does for a loop's element, the local is made to stand where its value lies instead of being
    // a copy: a write through it reaches what it was bound from, as it will once compiled. A
    // binding of a value this frame owns (a local, a by-value parameter) is the copy an owned match
    // makes, and so is one nothing after it may write through. True when this was such a store.
    bindBorrow &self inout a:Ast v:NodeId -> bool {
        e: Expr = a.expr(v);
        if (e.op != Op.Assignment || e.right == NO_NODE) { return false; }
        l: Expr = a.expr(e.left);
        if (l.op != Op.Lvalue || l.kind != Lit.Struct || namedScalar(l.kind, l.structName)) { return false; }
        n: Sym = NO_SYM;
        match l.payload { Name(x) { n = x; } _ { return false; } }
        r: Expr = a.expr(e.right);
        s: str = nameOf(n);
        addr: long = 0;
        if (strStartsWith(s, "$match") || strStartsWith(s, "$bmatch") || strStartsWith(s, "$tup")) {
            if ((r.op == Op.FunctionCall || r.op == Op.MethodCall) && r.kind == Lit.Ref) {
                // A borrow a call returned (`v.at(i)`): the local stands where it points.
                at: long = self.findLocal(n);
                if (at < 0) { return false; }
                addr = self.eval(a, e.right).bits;
                if (self.stopped) { return true; }
                self.slots.set(at, addr);
                self.aliased.set(at, true);
                return true;
            }
            // Any other call's result is the match's own value, and a literal the destructure's.
            if (r.op != Op.Lvalue && r.op != Op.FieldAccess && r.op != Op.ArrayIndex) { return false; }
            if (!strStartsWith(s, "$bmatch") && !self.lentPlace(a, e.right)) { return false; }
        } else {
            // A payload slot (`$Pt$0`), or an element (`$0`) of a destructure's hidden local: the
            // parser writes these, and only for a binding.
            if (r.op != Op.FieldAccess) { return false; }
            f: FieldNode = a.fields.get(0);
            match r.payload { Field(i) { f = a.fields.get(i); } _ { return false; } }
            if (!strStartsWith(nameOf(f.name), "$")) { return false; }
            if (isTupleField(f.name)) {
                b: Expr = a.expr(f.base);
                if (b.op != Op.Lvalue) { return false; }
                match b.payload { Name(x) { if (!strStartsWith(nameOf(x), "$tup")) { return false; } } _ { return false; } }
            }
            if (!self.lentPlace(a, f.base)) { return false; }
            if (!gReg.needsDrop(l.structName) && !self.mayWriteAfter(a, v, n)) { return false; }
        }
        at: long = self.findLocal(n);
        if (at < 0) { return false; }
        addr = self.place(a, e.right);
        if (self.stopped) { return true; }
        self.slots.set(at, addr);
        self.aliased.set(at, true);
        return true;
    }

    // Whether the place `id` names lies outside what this frame owns: in a borrow (a `Ref`
    // parameter or local), in a local that stands for another value (`aliased`), in a global, in
    // what a call's borrow or a pointer reaches.
    lentPlace &self inout a:Ast id:NodeId -> bool {
        cur: NodeId = id;
        while (cur != NO_NODE) {
            e: Expr = a.expr(cur);
            if (e.op == Op.Lvalue) {
                match e.payload {
                    Name(x) {
                        at: long = self.findLocal(x);
                        if (at < 0) { return true; }
                        return self.kinds.get(at) == Lit.Ref || self.aliased.get(at);
                    }
                    _ { }
                }
                return false;
            }
            if (e.op == Op.FunctionCall || e.op == Op.MethodCall) {
                return e.kind == Lit.Ref || e.kind == Lit.Ptr || e.kind == Lit.Slice;
            }
            if (e.op == Op.Deref) { return true; }
            match e.payload {
                Field(f) { cur = a.fields.get(f).base; }
                Index(i) {
                    ix: IndexNode = a.indexes.get(i);
                    if (ix.base == NO_NODE) {
                        at: long = self.findLocal(ix.name);
                        if (at < 0) { return true; }
                        return self.kinds.get(at) == Lit.Ref || self.aliased.get(at);
                    }
                    cur = ix.base;
                }
                Sub(v) { cur = v; }
                _ { return false; }
            }
        }
        return false;
    }

    // Whether the statements after store `v` (in the block `execBlock` is running) may write through
    // local `n`: a field of it assigned, it lent with `&`, it or a part of it handed to any call, a
    // `with` on it, a match on it, or a hidden local read out of it. Read off the tree once per store.
    // Wider than what the guard will decide (a call that only reads counts), which is the side of a
    // borrow: one only read reads the same where it lies, and nothing in the code after it writes
    // the value it lies in, or the binding would be refused for it.
    mayWriteAfter &self inout a:Ast v:NodeId n:Sym -> bool {
        key: long = v as long;
        hit: Option<bool> = self.writeAfter.find(key);
        match hit { Some(w) { return w; } None { } }
        w: bool = false;
        if (self.curBlock >= 0) {
            for k in self.curAt + 1..a.blockLen(self.curBlock) {
                if (self.stmtWrites(a, a.stmtAt(self.curBlock, k), n)) { w = true; break; }
            }
        }
        self.writeAfter.put(key, w);
        return w;
    }
    stmtWrites &self inout a:Ast st:Stmt n:Sym -> bool {
        if (st.kind == StmtKind.Match && a.matches.get(st.at).scrutinee == n) { return true; }
        if (st.kind == StmtKind.With && a.withs.get(st.at).name == n) { return true; }
        exprs: Vec<NodeId> = stmtExprs(a, st);
        for x in exprs { if (self.exprWrites(a, x, n)) { return true; } }
        kids: Vec<long> = childBlocks(a, st);
        for b in kids {
            if (b < 0) { continue; }
            for k in 0..a.blockLen(b) { if (self.stmtWrites(a, a.stmtAt(b, k), n)) { return true; } }
        }
        return false;
    }
    exprWrites &self inout a:Ast id:NodeId n:Sym -> bool {
        if (id == NO_NODE) { return false; }
        e: Expr = a.expr(id);
        if (e.op == Op.Assignment && rootedAt(a, e.left, n)) { return true; }
        if (e.op == Op.Assignment && rootedAt(a, e.right, n)) {
            // A hidden local read out of it: a match or a destructure, whose names may write it.
            match a.expr(e.left).payload {
                Name(x) {
                    s: str = nameOf(x);
                    if (strStartsWith(s, "$match") || strStartsWith(s, "$bmatch") || strStartsWith(s, "$tup")) { return true; }
                }
                _ { }
            }
        }
        if (e.op == Op.AddressOf && rootedAt(a, id, n)) { return true; }
        if (self.exprWrites(a, e.left, n) || self.exprWrites(a, e.right, n)) { return true; }
        match e.payload {
            Sub(x)   { return self.exprWrites(a, x, n); }
            Field(f) { return self.exprWrites(a, a.fields.get(f).base, n); }
            Index(i) {
                ix: IndexNode = a.indexes.get(i);
                return self.exprWrites(a, ix.base, n) || self.exprWrites(a, ix.index, n);
            }
            Call(c) {
                cn: CallNode = a.calls.get(c);
                if (rootedAt(a, cn.receiver, n)) { return true; }
                for k in 0..cn.argCount {
                    arg: NodeId = a.argAt(cn, k);
                    if (rootedAt(a, arg, n) || self.exprWrites(a, arg, n)) { return true; }
                }
                return self.exprWrites(a, cn.receiver, n);
            }
            Lit(l) {
                ln: LitNode = a.lits.get(l);
                for k in 0..ln.initCount { if (self.exprWrites(a, a.inits.get(ln.firstInit + k).value, n)) { return true; } }
                return self.exprWrites(a, ln.rest, n);
            }
            _ { }
        }
        return false;
    }

    // ─── places ──────────────────────────────────────────────────────────────

    // Where the value an expression denotes lives. A local is its slot (a borrow's slot holds the
    // address, and `baseAddress` is what follows it). A field or element is an offset from its
    // base, and a temporary is wherever it was just built.
    place &self inout a:Ast id:NodeId -> long {
        if (self.stopped) { return 0; }
        e: Expr = a.expr(id);
        if (e.op == Op.Lvalue) {
            match e.payload {
                Name(n) {
                    at: long = self.findLocal(n);
                    // A `&self` of a `str` is read as the str (the checker retypes the name), and
                    // its slot holds the pair's address, as the lowerer's by-pointer slot does.
                    if (at >= 0 && e.kind == Lit.Str && self.kinds.get(at) == Lit.Ref) {
                        return self.loadWord(self.slots.get(at));
                    }
                    if (at >= 0) { return self.slots.get(at); }
                    return self.globalPlace(a, n);
                }
                _ { }
            }
            return 0;
        }
        if (e.op == Op.FieldAccess) {
            f: FieldNode = a.fields.get(0);
            match e.payload { Field(i) { f = a.fields.get(i); } _ { } }
            base: long = self.baseAddress(a, f.base);
            if (self.stopped) { return 0; }
            return base + self.fieldOffset(a, f.base, f.name);
        }
        if (e.op == Op.ArrayIndex) { return self.elemAddress(a, id); }
        if (e.op == Op.Deref) {
            match e.payload { Sub(v) { return self.eval(a, v).bits; } _ { } }
            return 0;
        }
        // A temporary: a literal, a call's result, a `str`, a trait object.
        return self.eval(a, id).bits;
    }

    // The address a field is read out of: a pointer or a borrow holds it, anything else is it.
    baseAddress &self inout a:Ast id:NodeId -> long {
        k: Lit = a.expr(id).kind;
        if (k == Lit.Ptr || k == Lit.Ref) { return self.eval(a, id).bits; }
        return self.place(a, id);
    }

    fieldOffset &self inout a:Ast base:NodeId field:Sym -> long {
        b: Expr = a.expr(base);
        if (b.kind == Lit.Str || b.kind == Lit.Slice) {
            if (nameOf(field) == "ptr") { return 0; }
            return 8;
        }
        // Every field access a loop makes asks this, so the offset for (the base's type, the
        // field) is kept for the rest of this evaluation. Not longer, because layouts settle
        // between the checker's rounds. A pointer's type names its pointee in mangled form, which
        // is a name of its own, so the key keeps a pointer and its pointee apart.
        key: long = ((b.structName as long) << 32) | (field as long);
        hit: Option<long> = self.offsets.find(key);
        match hit { Some(o) { return o; } None { } }
        sname: Sym = b.structName;
        if (b.kind == Lit.Ptr && sname != NO_SYM) { sname = unmangledType(nameOf(sname)).name; }
        si: long = gReg.findStructSym(sname);
        if (si < 0) { self.stop(format("a field of `{}`, which it cannot lay out", nameOf(sname))); return 0; }
        d: StructDef = gReg.structDef(si);
        fi: long = gReg.findFieldSym(d, field);
        if (fi < 0) { self.stop(format("a field `{}` that `{}` does not have", nameOf(field), nameOf(sname))); return 0; }
        off: long = gReg.fieldAt(d, fi).offset;
        self.offsets.put(key, off);
        return off;
    }

    // `x[i]`: the element's address, bounds-checked against what the base declares. An index
    // the program would trap on at runtime is refused here, so it still traps there.
    elemAddress &self inout a:Ast id:NodeId -> long {
        e: Expr = a.expr(id);
        ix: IndexNode = a.indexes.get(0);
        match e.payload { Index(i) { ix = a.indexes.get(i); } _ { } }
        if (ix.whole || ix.sliceStart != NO_NODE || ix.sliceEnd != NO_NODE) { return self.sliceOf(a, ix); }
        w: long = typeBytes(e.kind, e.structName);
        i: long = self.eval(a, ix.index).bits;
        if (self.stopped) { return 0; }
        if (ix.base != NO_NODE) {
            b: Expr = a.expr(ix.base);
            // An array first: its node carries the element's type, so `t.spell[0]` over a
            // `[str; 8]` field reads as a `str` and would otherwise be indexed as one.
            n: long = self.arrayLength(a, ix.base);
            if (n >= 0) {
                base: long = self.place(a, ix.base);
                if (self.stopped) { return 0; }
                if (i < 0 || i >= n) { self.stop(stringOf("an index out of bounds")); return 0; }
                return base + i * w;
            }
            if (b.kind == Lit.Ptr || ix.rawPointerBase) { return self.eval(a, ix.base).bits + i * w; }
            if (b.kind == Lit.Str || b.kind == Lit.Slice) {
                pair: long = self.place(a, ix.base);
                if (self.stopped) { return 0; }
                len: long = self.loadWord(pair + 8);
                if (i < 0 || i >= len) { self.stop(stringOf("an index out of bounds")); return 0; }
                if (b.kind == Lit.Str) { w = 1; }
                return self.loadWord(pair) + i * w;
            }
            base: long = self.place(a, ix.base);
            if (self.stopped) { return 0; }
            return base + i * w;
        }
        at: long = self.findLocal(ix.name);
        if (at >= 0) {
            if (self.kinds.get(at) == Lit.Ptr && !self.arrays.get(at)) { return self.loadWord(self.slots.get(at)) + i * w; }
            if (i < 0 || i >= self.counts.get(at)) { self.stop(stringOf("an index out of bounds")); return 0; }
            return self.slots.get(at) + i * w;
        }
        gi: long = gReg.findGlobalSym(ix.name);
        if (gi < 0) { self.stop(format("an index into `{}`, which it does not hold", nameOf(ix.name))); return 0; }
        g: GlobalDef = gReg.globalDef(gi);
        if (i < 0 || i >= g.count) { self.stop(stringOf("an index out of bounds")); return 0; }
        return self.globalPlace(a, ix.name) + i * w;
    }
    // `x[..]` and `x[lo..hi]`: a fresh {ptr, len} pair over part of the base, which is a `str`'s
    // or a slice's own pair, an array's storage, or a raw pointer's target. A raw pointer has no
    // length of its own, so both bounds must be written. A bound the parser left out is 0 or the
    // base's length.
    sliceOf &self inout a:Ast ix:IndexNode -> long {
        base: NodeId = ix.base;
        ptr: long = 0;
        len: long = -1;
        w: long = 1;
        if (base == NO_NODE) {
            at: long = self.findLocal(ix.name);
            if (at >= 0) {
                ptr = self.slots.get(at); len = self.counts.get(at);
                w = typeBytes(self.kinds.get(at), self.snames.get(at));
            } else {
                gi: long = gReg.findGlobalSym(ix.name);
                if (gi < 0) { self.stop(format("a slice of `{}`, which it does not hold", nameOf(ix.name))); return 0; }
                g: GlobalDef = gReg.globalDef(gi);
                ptr = self.globalPlace(a, ix.name); len = g.count;
                w = typeBytes(g.kind, g.structName);
            }
        } else {
            b: Expr = a.expr(base);
            n: long = self.arrayLength(a, base);
            if (n >= 0) {
                ptr = self.place(a, base); len = n;
                w = typeBytes(b.kind, b.structName);
            } else if (b.kind == Lit.Str || b.kind == Lit.Slice) {
                pair: long = self.place(a, base);
                if (self.stopped) { return 0; }
                ptr = self.loadWord(pair); len = self.loadWord(pair + 8);
                if (b.kind == Lit.Slice) { w = namedWidth(b.structName); }
            } else if (b.kind == Lit.Ptr) {
                ptr = self.eval(a, base).bits;
                if (b.structName != NO_SYM) { t: TypeRef = unmangledType(nameOf(b.structName)); w = typeBytes(t.base, t.name); }
            } else {
                self.stop(format("a slice of a value of type `{}`", typeName(b.kind))); return 0;
            }
        }
        if (self.stopped) { return 0; }
        lo: long = 0;
        hi: long = len;
        if (ix.sliceStart != NO_NODE) { lo = self.eval(a, ix.sliceStart).bits; }
        if (self.stopped) { return 0; }
        if (ix.sliceEnd != NO_NODE) { hi = self.eval(a, ix.sliceEnd).bits; }
        if (self.stopped) { return 0; }
        if (hi < 0) { self.stop(stringOf("a slice of a raw pointer with no end")); return 0; }
        if (lo < 0 || hi < lo || (len >= 0 && hi > len)) { self.stop(stringOf("a slice out of bounds")); return 0; }
        pair: long = self.alloc(16);
        self.storeBits(pair, 8, ptr + lo * w);
        self.storeBits(pair + 8, 8, hi - lo);
        return pair;
    }
    // Where the bytes of a whole array lie. An array literal's value is its address, but a named
    // array or an array field has to be found by its place: its value is what its `kind` (the
    // element's) reads there, which is the first element rather than an address.
    arrayFrom &self inout a:Ast id:NodeId v:CtValue -> long {
        o: Op = a.expr(id).op;
        if (o == Op.Lvalue || o == Op.FieldAccess) { return self.place(a, id); }
        return v.bits;
    }

    // How many elements the base of an index has, when its declaration says: an array local, an
    // array global, an array field. -1 when nothing does.
    arrayLength &self inout a:Ast base:NodeId -> long {
        b: Expr = a.expr(base);
        if (b.op == Op.Lvalue) {
            match b.payload {
                Name(n) {
                    at: long = self.findLocal(n);
                    if (at >= 0) { if (self.arrays.get(at)) { return self.counts.get(at); } return -1; }
                    gi: long = gReg.findGlobalSym(n);
                    if (gi >= 0) { g: GlobalDef = gReg.globalDef(gi); if (g.isArray) { return g.count; } }
                }
                _ { }
            }
            return -1;
        }
        if (b.op == Op.FieldAccess) {
            f: FieldNode = a.fields.get(0);
            match b.payload { Field(i) { f = a.fields.get(i); } _ { } }
            ow: Expr = a.expr(f.base);
            sname: Sym = ow.structName;
            if (ow.kind == Lit.Ptr && sname != NO_SYM) { sname = unmangledType(nameOf(sname)).name; }
            si: long = gReg.findStructSym(sname);
            if (si < 0) { return -1; }
            d: StructDef = gReg.structDef(si);
            fi: long = gReg.findFieldSym(d, f.name);
            if (fi < 0) { return -1; }
            fd: FieldDef = gReg.fieldAt(d, fi);
            if (fd.isArray) { return fd.count; }
        }
        return -1;
    }

    // A global's storage, if the compiler can vouch for its contents: nothing that runs before
    // this initializer may write it.
    globalPlace &self inout a:Ast n:Sym -> long {
        hit: Option<long> = self.globalAddr.find(nameOf(n));
        addr: long = -1;
        match hit { Some(p) { addr = p; } None { } }
        if (addr < 0) {
            if (self.fnAt.has(n as long)) { return -1; }   // a function's name: a value, not a place
            self.stop(format("the variable `{}`, which is not in scope at compile time", nameOf(n))); return 0;
        }
        // A dependency's global: what its own compile folded it to, loaded on first read.
        if (isExternGlobal(n)) {
            if (!self.macroRun && self.poison.mayWrite(n)) {
                self.stop(format("the global `{}`, which an earlier initializer that runs at startup may write", nameOf(n)));
                return 0;
            }
            if (!self.extReady.has(nameOf(n))) {
                self.loadExternGlobal(a, n, addr);
                if (self.stopped) { return 0; }
            }
            return addr;
        }
        if (self.macroRun) {
            g: long = self.globalOf(addr);
            if (g >= 0 && !self.folded.get(g)) {
                // Its initializer, now, into the snapshot: what the global would hold once its
                // own turn at startup had come.
                d: VarDeclNode = a.decls.get(self.gDecls.get(g));
                self.folded.set(g, true);
                v: CtValue = self.eval(a, d.init);
                if (self.stopped) {
                    self.stop(format("the global `{}`, whose initializer could not run: it met {}", nameOf(n), self.refusal));
                    return 0;
                }
                self.committing = true;
                if (d.isArray) { self.copy(addr, self.arrayFrom(a, d.init, v), declaredBytesOf(d)); }
                else { self.assignTo(addr, d.kind, d.structName, v); }
                self.committing = false;
                if (self.stopped) { return 0; }
            }
            return addr;
        }
        if (self.poison.mayWrite(n)) {
            self.stop(format("the global `{}`, which an earlier initializer that runs at startup may write", nameOf(n)));
            return 0;
        }
        return addr;
    }

    // ─── expressions ─────────────────────────────────────────────────────────

    eval &self inout a:Ast id:NodeId -> CtValue {
        none: CtValue = CtValue { kind: Lit.Void, structName: NO_SYM, bits: 0 };
        if (!self.tick()) { return none; }
        if (id == NO_NODE) { return self.stop(stringOf("an empty expression")); }
        e: Expr = a.expr(id);
        if (e.left != NO_NODE) { return self.evalBinary(a, e); }
        if (e.op == Op.Literal) {
            if (!ctScalar(e.kind, e.structName)) { return self.stop(format("a literal of type `{}`", typeName(e.kind))); }
            match e.payload {
                Num(v) { return make(e.kind, e.structName, v); }
                // A float literal is its spelling, rounded here to the width it was given.
                Text(t) { if (isFloat(e.kind)) { return make(e.kind, e.structName, decimalToFloat(nameOf(t), e.kind == Lit.Float)); } }
                _ { }
            }
            return self.stop(stringOf("a literal with no value"));
        }
        if (e.op == Op.Lvalue) {
            // A function's name as a value: its handle.
            if (e.kind == Lit.Fn) {
                match e.payload {
                    Name(n) {
                        if (self.findLocal(n) < 0 && !self.globalAddr.has(nameOf(n))) { return self.fnValue(a, n, e.structName); }
                    }
                    _ { }
                }
            }
            addr: long = self.place(a, id);
            if (self.stopped) { return none; }
            return self.valueAt(addr, e.kind, e.structName);
        }
        if (e.op == Op.FieldAccess || e.op == Op.ArrayIndex || e.op == Op.Deref) {
            addr: long = self.place(a, id);
            if (self.stopped) { return none; }
            // `.ptr` out of a `str` or a slice is a raw address, as the lowerer has it: its
            // arithmetic counts bytes, whatever companion name a slice's node carries.
            if (e.op == Op.FieldAccess && e.kind == Lit.Ptr) {
                f: FieldNode = a.fields.get(0);
                match e.payload { Field(i) { f = a.fields.get(i); } _ { } }
                bk: Lit = a.expr(f.base).kind;
                if ((bk == Lit.Str || bk == Lit.Slice) && nameOf(f.name) == "ptr") { return self.valueAt(addr, Lit.Ptr, NO_SYM); }
            }
            return self.valueAt(addr, e.kind, e.structName);
        }
        if (e.op == Op.StringLit) {
            match e.payload { Text(t) { return CtValue { kind: Lit.Str, structName: NO_SYM, bits: self.literal(t) }; } _ { } }
            return none;
        }
        if (e.op == Op.StructLit || e.op == Op.TupleLit) { return self.buildLiteral(a, e); }
        if (e.op == Op.ArrayLit) { return self.buildArray(a, e); }
        if (e.op == Op.Cast) {
            match e.payload {
                Sub(v) {
                    x: CtValue = self.eval(a, v);
                    if (self.stopped) { return none; }
                    // Between a pointer and an integer a cast is the bits: every address here
                    // is the evaluator's own and the same on every build.
                    // A word cast to a fn value (`slot[0] as fn(long, Write)->void`, reading what
                    // a `methodTable` holds) keeps its bits, so it is a handle only if it was one.
                    if (e.kind == Lit.Ptr || e.kind == Lit.Ref || e.kind == Lit.Fn) { return CtValue { kind: e.kind, structName: e.structName, bits: x.bits }; }
                    // `s as [u8]` reads one fat pointer as another: the same pair, typed differently.
                    if ((e.kind == Lit.Str || e.kind == Lit.Slice) && (x.kind == Lit.Str || x.kind == Lit.Slice)) {
                        return CtValue { kind: e.kind, structName: e.structName, bits: x.bits };
                    }
                    if (!ctScalar(e.kind, e.structName)) { return self.stop(format("a cast to `{}`", typeName(e.kind))); }
                    return make(e.kind, e.structName, convertBits(x.bits, storedKind(x.kind, x.structName), storedKind(e.kind, e.structName)));
                }
                _ { }
            }
            return none;
        }
        if (e.op == Op.LogicalNot || e.op == Op.BitwiseNot) {
            match e.payload {
                Sub(v) {
                    x: CtValue = self.eval(a, v);
                    if (self.stopped) { return none; }
                    if (e.op == Op.LogicalNot) { return make(Lit.Bool, NO_SYM, boolBits(x.bits == 0)); }
                    return make(x.kind, x.structName, ~x.bits);
                }
                _ { }
            }
            return none;
        }
        if (e.op == Op.AddressOf) {
            match e.payload {
                Sub(v) {
                    if (e.kind == Lit.Fn) {
                        inner: Expr = a.expr(v);
                        match inner.payload { Name(n) { return self.fnValue(a, n, e.structName); } _ { } }
                    }
                    addr: long = self.place(a, v);
                    if (self.stopped) { return none; }
                    return CtValue { kind: e.kind, structName: e.structName, bits: addr };
                }
                _ { }
            }
            return self.stop(stringOf("an address of nothing"));
        }
        if (e.op == Op.Sizeof) {
            t: Expr = a.measuredOf(id);
            return make(Lit.Long, NO_SYM, typeBytes(t.kind, t.structName));
        }
        if (e.op == Op.FunctionCall || e.op == Op.MethodCall) {
            match e.payload { Call(c) { return self.call(a, a.calls.get(c)); } _ { } }
            return none;
        }
        if (e.op == Op.MakeTraitObj) {
            match e.payload { Sub(v) { return self.traitObject(a, v, e.structName); } _ { } }
            return none;
        }
        return self.stop(format("an expression it does not know (operator {})", e.op as long));
    }

    // A function's value: its handle, FN_BASE plus its index.
    fnValue &self inout a:Ast n:Sym sig:Sym -> CtValue {
        hit: Option<long> = self.fnAt.find(n as long);
        match hit { Some(i) { return CtValue { kind: Lit.Fn, structName: sig, bits: FN_BASE + i }; } None { } }
        return self.stop(format("the address of `{}`, which is not a function the program holds", nameOf(n)));
    }

    // Builds the `{data, vtable}` pair for a concrete value seen as a trait object. The data is
    // where the value is (for a borrow, the address it holds), and the vtable is a handle naming
    // (concrete, trait), which dispatch reads and promotion turns into the table's label.
    traitObject &self inout a:Ast inner:NodeId trait:Sym -> CtValue {
        none: CtValue = CtValue { kind: Lit.Void, structName: NO_SYM, bits: 0 };
        data: long = self.baseAddress(a, inner);
        if (self.stopped) { return none; }
        concrete: Sym = a.expr(inner).structName;
        pair: long = self.alloc(16);
        self.storeBits(pair, 8, data);
        self.storeBits(pair + 8, 8, self.vtableHandle(concrete, trait));
        return CtValue { kind: Lit.TraitObj, structName: trait, bits: pair };
    }
    vtableHandle &self concrete:Sym trait:Sym -> long {
        for i in 0..self.vtConcrete.len() {
            if (self.vtConcrete.get(i) == concrete && self.vtTrait.get(i) == trait) { return VT_BASE + i; }
        }
        self.vtConcrete.push(concrete);
        self.vtTrait.push(trait);
        return VT_BASE + self.vtConcrete.len() - 1;
    }

    // What lives at an address, as a value: a scalar is loaded, an aggregate is its address, a
    // pointer, a borrow or a function value is the word held there.
    valueAt &self addr:long kind:Lit sname:Sym -> CtValue {
        if (ctScalar(kind, sname)) { return CtValue { kind: kind, structName: sname, bits: self.load(addr, kind, sname) }; }
        if (kind == Lit.Ptr || kind == Lit.Ref || kind == Lit.Fn) { return CtValue { kind: kind, structName: sname, bits: self.loadWord(addr) }; }
        if (kind == Lit.Struct || kind == Lit.Tuple || kind == Lit.Str || kind == Lit.Slice || kind == Lit.TraitObj) {
            return CtValue { kind: kind, structName: sname, bits: addr };
        }
        return self.stop(format("a value of type `{}`", typeName(kind)));
    }

    // Store a value where a place of this type is: a scalar at its width, an aggregate by copy,
    // a concrete struct into a trait-object slot as the {data, vtable} pair it becomes there.
    assignTo &self addr:long kind:Lit sname:Sym v:CtValue -> void {
        if (ctScalar(kind, sname)) { self.store(addr, kind, sname, v.bits); return; }
        if (kind == Lit.Ptr || kind == Lit.Ref || kind == Lit.Fn) { self.storeBits(addr, 8, v.bits); return; }
        if (kind == Lit.TraitObj && (v.kind == Lit.Struct || v.kind == Lit.Ref)) {
            self.storeBits(addr, 8, v.bits);
            self.storeBits(addr + 8, 8, self.vtableHandle(v.structName, sname));
            return;
        }
        if (kind == Lit.Struct || kind == Lit.Tuple || kind == Lit.Str || kind == Lit.Slice || kind == Lit.TraitObj) {
            self.copy(addr, v.bits, typeBytes(kind, sname));
            return;
        }
        self.stop(format("a store of type `{}`", typeName(kind)));
    }

    // `T { f: v, ... }`, `E.V(a, b)`, `(a, b)`: fresh zeroed storage, then each named field. A
    // partial literal leaves the rest zero, as at runtime; `..rest` copies it first.
    buildLiteral &self inout a:Ast e:Expr -> CtValue {
        none: CtValue = CtValue { kind: Lit.Void, structName: NO_SYM, bits: 0 };
        l: LitNode = a.lits.get(0);
        match e.payload { Lit(i) { l = a.lits.get(i); } _ { } }
        sname: Sym = e.structName;
        if (sname == NO_SYM) { sname = l.typeName; }
        si: long = gReg.findStructSym(sname);
        if (si < 0) { return self.stop(format("a literal of `{}`, which it cannot lay out", nameOf(sname))); }
        d: StructDef = gReg.structDef(si);
        addr: long = self.alloc(d.size);
        if (l.rest != NO_NODE) {
            r: long = self.place(a, l.rest);
            if (self.stopped) { return none; }
            self.copy(addr, r, d.size);
        }
        for k in 0..l.initCount {
            in: InitNode = a.inits.get(l.firstInit + k);
            fi: long = k;                      // a tuple names nothing: positional
            if (in.name != NO_SYM) { fi = gReg.findFieldSym(d, in.name); }
            if (fi < 0 || fi >= d.fieldCount) { return self.stop(format("a field `{}` that `{}` does not have", nameOf(in.name), nameOf(sname))); }
            fd: FieldDef = gReg.fieldAt(d, fi);
            v: CtValue = self.eval(a, in.value);
            if (self.stopped) { return none; }
            if (fd.isArray) { self.copy(addr + fd.offset, self.arrayFrom(a, in.value, v), fd.count * typeBytes(fd.kind, fd.structName)); }
            else { self.assignTo(addr + fd.offset, fd.kind, fd.structName, v); }
            if (self.stopped) { return none; }
        }
        return CtValue { kind: e.kind, structName: sname, bits: addr };
    }

    // `[a, b, c]`, a global array's initializer: the elements back to back, each stored as its
    // type is (`kind`/`structName` name the element). An array's value is its bytes' address,
    // which the global's own storage is copied from.
    buildArray &self inout a:Ast e:Expr -> CtValue {
        none: CtValue = CtValue { kind: Lit.Void, structName: NO_SYM, bits: 0 };
        l: LitNode = a.lits.get(0);
        match e.payload { Lit(i) { l = a.lits.get(i); } _ { } }
        w: long = typeBytes(e.kind, e.structName);
        addr: long = self.alloc(w * l.initCount + 8);
        for k in 0..l.initCount {
            v: CtValue = self.eval(a, a.inits.get(l.firstInit + k).value);
            if (self.stopped) { return none; }
            self.assignTo(addr + k * w, e.kind, e.structName, v);
            if (self.stopped) { return none; }
        }
        return CtValue { kind: e.kind, structName: e.structName, bits: addr };
    }

    evalBinary &self inout a:Ast e:Expr -> CtValue {
        none: CtValue = CtValue { kind: Lit.Void, structName: NO_SYM, bits: 0 };
        if (e.op == Op.Assignment) {
            v: CtValue = self.eval(a, e.right);
            if (self.stopped) { return none; }
            l: Expr = a.expr(e.left);
            addr: long = self.place(a, e.left);
            if (self.stopped) { return none; }
            // A whole fixed array: every element, from where the source array lies.
            n: long = self.arrayLength(a, e.left);
            if (n >= 0) {
                self.copy(addr, self.arrayFrom(a, e.right, v), n * typeBytes(l.kind, l.structName));
                return v;
            }
            self.assignTo(addr, l.kind, l.structName, v);
            if (self.stopped) { return none; }
            return self.valueAt(addr, l.kind, l.structName);
        }
        // `&&` and `||` read their right operand only when the left leaves the answer open.
        if (e.op == Op.LogicalAnd || e.op == Op.LogicalOr) {
            l: CtValue = self.eval(a, e.left);
            if (self.stopped) { return none; }
            if (e.op == Op.LogicalAnd && l.bits == 0) { return make(Lit.Bool, NO_SYM, 0); }
            if (e.op == Op.LogicalOr && l.bits != 0) { return make(Lit.Bool, NO_SYM, 1); }
            r: CtValue = self.eval(a, e.right);
            if (self.stopped) { return none; }
            return make(Lit.Bool, NO_SYM, boolBits(r.bits != 0));
        }
        l: CtValue = self.eval(a, e.left);
        if (self.stopped) { return none; }
        r: CtValue = self.eval(a, e.right);
        if (self.stopped) { return none; }
        // Floats, as the machine computes them (`support::fp` runs the same SSE instructions).
        fk: Lit = storedKind(r.kind, r.structName);
        if (isFloat(fk) || isFloat(storedKind(l.kind, l.structName))) {
            if (!isFloat(fk)) { fk = storedKind(l.kind, l.structName); }
            single: bool = fk == Lit.Float;
            le: Expr = a.expr(e.left);
            if (e.op == Op.Subtraction && isNegationMark(le)) {
                // `-x`: the sign flipped, a zero's and a NaN's included.
                if (single) { return make(fk, NO_SYM, r.bits ^ F32_SIGN); }
                return make(fk, NO_SYM, r.bits ^ F64_SIGN);
            }
            ar: long = -1;
            if (e.op == Op.Addition) { ar = 0; }
            else if (e.op == Op.Subtraction) { ar = 1; }
            else if (e.op == Op.Multiplication) { ar = 2; }
            else if (e.op == Op.Division) { ar = 3; }
            if (ar >= 0) {
                if (single) { return make(fk, NO_SYM, f32Arith(ar, l.bits, r.bits)); }
                return make(fk, NO_SYM, f64Arith(ar, l.bits, r.bits));
            }
            co: long = -1;
            if (e.op == Op.IsEqual) { co = 0; }
            else if (e.op == Op.IsNotEqual) { co = 1; }
            else if (e.op == Op.LessThan) { co = 2; }
            else if (e.op == Op.IsLessOrEqual) { co = 3; }
            else if (e.op == Op.GreaterThan) { co = 4; }
            else if (e.op == Op.IsGreaterOrEqual) { co = 5; }
            if (co >= 0) { return make(Lit.Bool, NO_SYM, boolBits(fpCompare(co, l.bits, r.bits, single))); }
            return self.stop(format("an operator over a value of type `{}`", typeName(fk)));
        }
        // Pointer arithmetic strides by the pointee, as at runtime; the difference of two
        // pointers is an element count.
        if (l.kind == Lit.Ptr || r.kind == Lit.Ptr) {
            if (e.op == Op.Addition || e.op == Op.Subtraction) {
                if (l.kind == Lit.Ptr && r.kind == Lit.Ptr) {
                    if (e.op != Op.Subtraction) { return self.stop(stringOf("two pointers added")); }
                    w: long = strideOf(l.structName);
                    return make(Lit.Long, NO_SYM, (l.bits - r.bits) / w);
                }
                p: CtValue = l;
                n: CtValue = r;
                if (r.kind == Lit.Ptr) { p = r; n = l; }
                w: long = strideOf(p.structName);
                if (e.op == Op.Subtraction) { return CtValue { kind: Lit.Ptr, structName: p.structName, bits: p.bits - n.bits * w }; }
                return CtValue { kind: Lit.Ptr, structName: p.structName, bits: p.bits + n.bits * w };
            }
            l = CtValue { kind: Lit.Long, structName: NO_SYM, bits: l.bits };
            r = CtValue { kind: Lit.Long, structName: NO_SYM, bits: r.bits };
        }
        if (l.kind == Lit.Ref || l.kind == Lit.Fn) { l = CtValue { kind: Lit.Long, structName: NO_SYM, bits: l.bits }; }
        if (r.kind == Lit.Ref || r.kind == Lit.Fn) { r = CtValue { kind: Lit.Long, structName: NO_SYM, bits: r.bits }; }
        if (!ctScalar(l.kind, l.structName) || !ctScalar(r.kind, r.structName)) {
            return self.stop(format("an operator over a value of type `{}`", typeName(l.kind)));
        }
        // The result's type is the operation's, as the checker decided; a comparison is at the
        // operands' width and signedness and yields a bool.
        t: Lit = storedKind(e.kind, e.structName);
        if (!(isInteger(t) || t == Lit.Bool)) { t = higherPrecedence(storedKind(l.kind, l.structName), storedKind(r.kind, r.structName)); }
        // A comparison orders at the operands' common type, as the lowerer's `commonKind` does:
        // a `u8` against a `char` meets at `i16`, so 200 is not below -1.
        uns: bool = isUnsignedInt(higherPrecedence(storedKind(l.kind, l.structName), storedKind(r.kind, r.structName)));
        if (e.op == Op.Addition)       { return make(t, NO_SYM, l.bits + r.bits); }
        if (e.op == Op.Subtraction)    { return make(t, NO_SYM, l.bits - r.bits); }
        if (e.op == Op.Multiplication) { return make(t, NO_SYM, l.bits * r.bits); }
        if (e.op == Op.Division || e.op == Op.Modulus) {
            if (r.bits == 0) { return self.stop(stringOf("a division by zero")); }
            if (isUnsignedInt(t)) {
                lu: u64 = l.bits as u64;
                ru: u64 = r.bits as u64;
                if (e.op == Op.Division) { return make(t, NO_SYM, (lu / ru) as long); }
                return make(t, NO_SYM, (lu % ru) as long);
            }
            if (e.op == Op.Division) { return make(t, NO_SYM, l.bits / r.bits); }
            return make(t, NO_SYM, l.bits % r.bits);
        }
        if (e.op == Op.BitwiseAnd) { return make(t, NO_SYM, l.bits & r.bits); }
        if (e.op == Op.BitwiseOr)  { return make(t, NO_SYM, l.bits | r.bits); }
        if (e.op == Op.BitwiseXor) { return make(t, NO_SYM, l.bits ^ r.bits); }
        if (e.op == Op.ShiftLeft)  { return make(t, NO_SYM, l.bits << (r.bits & 63)); }
        if (e.op == Op.ShiftRight) {
            if (isUnsignedInt(t)) { return make(t, NO_SYM, ((l.bits as u64) >> ((r.bits & 63) as u64)) as long); }
            return make(t, NO_SYM, l.bits >> (r.bits & 63));
        }
        if (e.op == Op.IsEqual)    { return make(Lit.Bool, NO_SYM, boolBits(l.bits == r.bits)); }
        if (e.op == Op.IsNotEqual) { return make(Lit.Bool, NO_SYM, boolBits(l.bits != r.bits)); }
        if (uns) {
            lu: u64 = l.bits as u64;
            ru: u64 = r.bits as u64;
            if (e.op == Op.LessThan)         { return make(Lit.Bool, NO_SYM, boolBits(lu < ru)); }
            if (e.op == Op.GreaterThan)      { return make(Lit.Bool, NO_SYM, boolBits(lu > ru)); }
            if (e.op == Op.IsLessOrEqual)    { return make(Lit.Bool, NO_SYM, boolBits(lu <= ru)); }
            if (e.op == Op.IsGreaterOrEqual) { return make(Lit.Bool, NO_SYM, boolBits(lu >= ru)); }
        } else {
            if (e.op == Op.LessThan)         { return make(Lit.Bool, NO_SYM, boolBits(l.bits < r.bits)); }
            if (e.op == Op.GreaterThan)      { return make(Lit.Bool, NO_SYM, boolBits(l.bits > r.bits)); }
            if (e.op == Op.IsLessOrEqual)    { return make(Lit.Bool, NO_SYM, boolBits(l.bits <= r.bits)); }
            if (e.op == Op.IsGreaterOrEqual) { return make(Lit.Bool, NO_SYM, boolBits(l.bits >= r.bits)); }
        }
        return self.stop(format("an operator it does not know ({})", e.op as long));
    }

    // ─── calls ───────────────────────────────────────────────────────────────

    // A call is direct by name, through a function value (`SLOT_FNPTR`, the value a variable or
    // an expression holds), or dispatched through a trait object, whose vtable handle names the
    // impl while the call's slot names the method. Every one ends in `invoke`.
    call &self inout a:Ast c:CallNode -> CtValue {
        none: CtValue = CtValue { kind: Lit.Void, structName: NO_SYM, bits: 0 };
        if (c.slot == SLOT_FNPTR) {
            fv: long = 0;
            if (c.callee != NO_NODE) { fv = self.eval(a, c.callee).bits; }
            else {
                at: long = self.findLocal(c.name);
                if (at >= 0) { fv = self.loadWord(self.slots.get(at)); }
                else { fv = self.loadWord(self.globalPlace(a, c.name)); }
            }
            if (self.stopped) { return none; }
            if (fv < FN_BASE || fv >= VT_BASE || fv - FN_BASE >= a.fns.len()) { return self.stop(stringOf("a call through a value that names no function")); }
            nodes: Vec<NodeId>;
            for k in 0..c.argCount { nodes.push(a.argAt(c, k)); }
            return self.invoke(a, fv - FN_BASE, nodes);
        }
        if (c.slot != NO_SLOT) {
            obj: long = self.place(a, c.receiver);
            if (self.stopped) { return none; }
            data: long = self.loadWord(obj);
            h: long = self.loadWord(obj + 8);
            if (self.stopped) { return none; }
            if (h < VT_BASE || h - VT_BASE >= self.vtConcrete.len()) { return self.stop(stringOf("a dispatch through a trait object with no vtable")); }
            concrete: Sym = self.vtConcrete.get(h - VT_BASE);
            trait: Sym = self.vtTrait.get(h - VT_BASE);
            ii: long = gReg.findImplMangled(concrete, trait);
            if (ii < 0) { return self.stop(format("a dispatch to `{}` as `{}`, which nothing implements", nameOf(concrete), nameOf(trait))); }
            im: TraitImplDef = gReg.implAt(ii);
            ti: long = gReg.findTraitSym(im.trait.name);
            if (ti < 0) { return self.stop(format("a dispatch through `{}`, a trait it cannot find", nameOf(trait))); }
            t: TraitDef = gReg.traitDef(ti);
            if (c.slot < 0 || c.slot >= t.methodCount) { return self.stop(stringOf("a dispatch past the vtable's end")); }
            m: Sym = implMethodName(im, gReg.traitMethodAt(t, c.slot).name);
            mh: Option<long> = self.fnAt.find(m as long);
            fi: long = -1;
            match mh { Some(i) { fi = i; } None { } }
            if (fi < 0) { return self.stop(format("a dispatch to `{}`, whose body the compiler does not hold", nameOf(m))); }
            nodes: Vec<NodeId>;
            for k in 0..c.argCount { nodes.push(a.argAt(c, k)); }
            return self.invokeWithSelf(a, fi, data, nodes);
        }
        hit: Option<long> = self.fnAt.find(c.name as long);
        at: long = -1;
        match hit { Some(i) { at = i; } None { } }
        if (at < 0) { return self.stop(format("a call to `{}`, whose body the compiler does not hold (a syscall, or an external function)", nameOf(c.name))); }
        bk: long = builtinOf(a.fns.get(at));
        if (bk != 0) { return self.builtin(a, at, bk, c); }
        nodes: Vec<NodeId>;
        if (c.receiver != NO_NODE) { nodes.push(c.receiver); }
        for k in 0..c.argCount { nodes.push(a.argAt(c, k)); }
        return self.invoke(a, at, nodes);
    }

    // ─── builtins: declarations whose bodies the compiler provides ───────────
    //
    // A builtin is found by its declaration (`builtin name ...;`, with its kind on the node),
    // never by how its name is spelled.
    builtin &self inout a:Ast at:long bk:long c:CallNode -> CtValue {
        none: CtValue = CtValue { kind: Lit.Void, structName: NO_SYM, bits: 0 };
        if (!self.tick()) { return none; }
        // `atCompileTime()`: here, yes. The lowerer answers no, and the optimizer drops the branch.
        if (bk == BI_AT_COMPILE_TIME) { return CtValue { kind: Lit.Bool, structName: NO_SYM, bits: 1 }; }
        if (bk == BI_PARSE_EXPR) {
            src: CtValue = self.eval(a, a.argAt(c, 0));
            if (self.stopped) { return none; }
            return CtValue { kind: Lit.Struct, structName: a.fns.get(at).returnStruct, bits: self.parseSnippet(src.bits) };
        }
        if (bk == BI_EXIT) {
            st: CtValue = self.eval(a, a.argAt(c, 0));
            if (self.stopped) { return none; }
            return self.ctExit(st.bits);
        }
        if (bk == BI_SYSCALL) {
            args: Vec<long>;
            for k in 0..c.argCount {
                v: CtValue = self.eval(a, a.argAt(c, k));
                if (self.stopped) { return none; }
                args.push(v.bits);
            }
            r: long = self.ctSyscall(args);
            if (self.stopped) { return none; }
            return CtValue { kind: Lit.Long, structName: NO_SYM, bits: r };
        }
        // An atomic: the evaluator runs one thread, so it is the plain access it stands for.
        if (isAtomicBuiltin(bk)) {
            vals: Vec<long>;
            for k in 0..c.argCount {
                v: CtValue = self.eval(a, a.argAt(c, k));
                if (self.stopped) { return none; }
                vals.push(v.bits);
            }
            op: long = atomicOpOf(bk);
            k: Lit = Lit.Long;
            if (op != bk) { k = Lit.Int; }
            p: long = vals.get(0);
            if (op == BI_ATOMIC_STORE || op == BI_ATOMIC_STORE_SC) { self.store(p, k, NO_SYM, vals.get(1)); return none; }
            old: long = self.load(p, k, NO_SYM);
            if (self.stopped) { return none; }
            if (op == BI_ATOMIC_SWAP) { self.store(p, k, NO_SYM, vals.get(1)); }
            if (op == BI_ATOMIC_ADD) { self.store(p, k, NO_SYM, wrapTo(old + vals.get(1), k)); }
            if (op == BI_ATOMIC_CAS && old == wrapTo(vals.get(1), k)) { self.store(p, k, NO_SYM, vals.get(2)); }
            if (self.stopped) { return none; }
            return CtValue { kind: k, structName: NO_SYM, bits: old };
        }
        // A block copy, a byte at a time.
        if (bk == BI_MEMCPY) {
            vals: Vec<long>;
            for k in 0..c.argCount {
                v: CtValue = self.eval(a, a.argAt(c, k));
                if (self.stopped) { return none; }
                vals.push(v.bits);
            }
            for i in 0..vals.get(2) {
                b: long = self.load(vals.get(1) + i, Lit.U8, NO_SYM);
                if (self.stopped) { return none; }
                self.store(vals.get(0) + i, Lit.U8, NO_SYM, b);
                if (self.stopped || !self.tick()) { return none; }
            }
            return none;
        }
        return self.stop(format("a builtin it does not know ({})", bk));
    }

    // The operating system that compile-time code runs on. It offers anonymous memory (`mmap`,
    // `munmap` and `mremap` over the compile-time heap, each mapping a fresh zeroed block),
    // writes to stderr (kept, and used as the error's text if the code then exits), and
    // `exit`/`exit_group`, which end the evaluation as the program's own decision. Nothing else:
    // a read, a file, a clock or a thread would make what folds differ between builds, so any
    // other call is refused by name.
    ctSyscall &self args:Vec<long> -> long {
        nr: long = args.get(0);
        a1: long = 0; a2: long = 0; a3: long = 0; a4: long = 0; a5: long = 0;
        if (args.len() > 1) { a1 = args.get(1); }
        if (args.len() > 2) { a2 = args.get(2); }
        if (args.len() > 3) { a3 = args.get(3); }
        if (args.len() > 4) { a4 = args.get(4); }
        if (args.len() > 5) { a5 = args.get(5); }
        if (nr == SYS_WRITE) {
            if (a1 == 1) {
                self.stop(stringOf("a write to stdout (fd 1): compile-time code has no output, though what it writes to stderr (fd 2) becomes the error if it then exits"));
                return 0;
            }
            if (a1 != 2) { self.stop(format("a write to file descriptor {}: compile-time code writes only to stderr (fd 2)", a1)); return 0; }
            if (a3 < 0) { return -22; }
            if (a3 > 0 && !self.inBounds(a2, a3)) { self.stop(stringOf("a write from outside compile-time memory")); return 0; }
            for i in 0..a3 { self.ctErr.push(self.rawByte(a2 + i) as char); }
            return a3;
        }
        if (nr == SYS_MMAP) {
            if ((a4 & MAP_ANONYMOUS) == 0 || a5 != -1) { self.stop(stringOf("an `mmap` of a file: compile-time code may map only anonymous memory")); return 0; }
            if ((a4 & MAP_FIXED) != 0) { self.stop(stringOf("an `mmap` at a fixed address: compile-time memory is the compiler's to place")); return 0; }
            if (a2 <= 0) { return -22; }
            return self.ctMalloc(a2);
        }
        if (nr == SYS_MUNMAP) {
            if (!self.mappingAt(a1)) {
                self.stop(stringOf("an `munmap` of memory `mmap` did not hand out (compile-time code unmaps a whole mapping, from its start)"));
                return 0;
            }
            self.ctFree(a1);
            return 0;
        }
        if (nr == SYS_MREMAP) {
            if (!self.mappingAt(a1)) { self.stop(stringOf("an `mremap` of memory `mmap` did not hand out")); return 0; }
            if ((a4 & MREMAP_FIXED) != 0) { self.stop(stringOf("an `mremap` to a fixed address: compile-time memory is the compiler's to place")); return 0; }
            have: long = self.blocks.get(self.blockOf(a1)).size;
            if (a3 <= have) { return a1; }
            if ((a4 & MREMAP_MAYMOVE) == 0) { return -12; }
            q: long = self.ctMalloc(a3);
            if (self.stopped) { return 0; }
            keep: long = a2;
            if (keep > have) { keep = have; }
            self.copy(q, a1, keep);
            self.ctFree(a1);
            return q;
        }
        if (nr == SYS_EXIT || nr == SYS_EXIT_GROUP) { self.ctExit(a1); return 0; }
        // The rule goes on a note line of its own. A refusal always ends the first line of the
        // message it is spliced into, so the note lands under the error where it belongs.
        self.stop(format("the syscall {}{}
note: compile-time code may only map memory, write to stderr and exit, so that every build computes the same result",
                         nr, syscallNote(nr)));
        return 0;
    }
    // A live block that starts at `p`: what an `mmap` handed out.
    mappingAt &self p:long -> bool {
        b: long = self.blockOf(p);
        return b >= 0 && self.blocks.get(b).start == p && self.blocks.get(b).live;
    }

    // The code ended itself. The evaluation stops, and its error is what the code wrote to
    // stderr (a `panic`'s "panic: ..." line, a derive's `refuse` reason), or its exit status when
    // it wrote nothing. `refused` marks this as the code's own decision rather than a limit the
    // evaluator met.
    ctExit &self status:long -> CtValue {
        text: String;
        bytes: str = "";
        unsafe { bytes = self.ctErr.view(); }
        n: long = bytes.len;
        while (n > 0 && (bytes[n - 1] == 10 || bytes[n - 1] == 32)) { n = n - 1; }
        text.pushStr(strSlice(bytes, 0, n));
        if (n == 0) { text.pushString(format("an exit with status {}", status)); }
        self.stop(text);
        self.refused = true;
        return CtValue { kind: Lit.Void, structName: NO_SYM, bits: 0 };
    }

    // A method's receiver is its first argument. A struct parameter arrives by value, as a copy
    // of the caller's bytes into the callee's own slot, and a borrow (`&self`, `inout`, or a read
    // parameter the checker retyped) arrives as the address: exactly the split the prologue
    // makes. An aggregate result is built where the caller made room for it, before the callee's
    // frame goes away.
    invoke &self inout a:Ast at:long nodes:Vec<NodeId> -> CtValue {
        none: CtValue = CtValue { kind: Lit.Void, structName: NO_SYM, bits: 0 };
        f: FnNode = a.fns.get(at);
        if (f.isTemplate) { return self.stop(format("a call to `{}`, which is a template", nameOf(f.name))); }
        // A trailing `...T` takes every remaining argument: they are packed into a slice the way
        // the call builds one on the stack, and the slice is the parameter's value.
        fixed: long = f.argCount;
        if (f.argCount > 0 && a.paramAt(f, f.argCount - 1).isVariadic) { fixed = f.argCount - 1; }
        if (nodes.len() < fixed || (fixed == f.argCount && nodes.len() != fixed)) {
            return self.stop(format("a call to `{}` with the wrong number of arguments", nameOf(f.name)));
        }
        vals: Vec<CtValue>;
        for k in 0..fixed {
            vals.push(self.argValue(a, a.paramAt(f, k), nodes.get(k)));
            if (self.stopped) { return none; }
        }
        if (fixed < f.argCount) {
            vals.push(self.packVariadic(a, a.paramAt(f, fixed), nodes, fixed));
            if (self.stopped) { return none; }
        }
        return self.run(a, at, vals);
    }
    packVariadic &self inout a:Ast p:VarDeclNode nodes:Vec<NodeId> from:long -> CtValue {
        none: CtValue = CtValue { kind: Lit.Void, structName: NO_SYM, bits: 0 };
        if (p.elemKind == Lit.Any) { return self.packAny(a, p, nodes, from); }
        n: long = nodes.len() - from;
        w: long = typeBytes(p.elemKind, p.elemStruct);
        buf: long = self.alloc(n * w);
        for k in 0..n {
            v: CtValue = self.eval(a, nodes.get(from + k));
            if (self.stopped) { return none; }
            if (ctScalar(p.elemKind, p.elemStruct) || p.elemKind == Lit.Ptr || p.elemKind == Lit.Fn || p.elemKind == Lit.Ref) {
                self.store(buf + k * w, p.elemKind, p.elemStruct, v.bits);
            } else {
                self.copy(buf + k * w, v.bits, w);
            }
        }
        pair: long = self.alloc(16);
        self.storeBits(pair, 8, buf);
        self.storeBits(pair + 8, 8, n);
        return CtValue { kind: Lit.Slice, structName: p.structName, bits: pair };
    }
    // Boxes a `...any` run the way the lowerer does (`Lowerer.boxAny`), so `format` and its kin
    // run here unchanged. Each argument takes 24 bytes, {tag, x, y}, as `stdlib/fmt.k`'s `AnyBox`
    // reads them. A `str` is its pointer and length; a value whose type implements `Display`, or
    // a `Display` object, is its address and a vtable whose slot 0 `callDisplay` reads; anything
    // else is its value, tagged by width and signedness.
    packAny &self inout a:Ast p:VarDeclNode nodes:Vec<NodeId> from:long -> CtValue {
        none: CtValue = CtValue { kind: Lit.Void, structName: NO_SYM, bits: 0 };
        n: long = nodes.len() - from;
        buf: long = self.alloc(n * 24);
        for k in 0..n {
            arg: NodeId = nodes.get(from + k);
            at: long = buf + k * 24;
            e: Expr = a.expr(arg);
            isObj: bool = e.kind == Lit.TraitObj && lastComponentOf(nameOf(e.structName)) == "Display";
            isVal: bool = (e.kind == Lit.Struct || e.kind == Lit.Ref) && e.structName != NO_SYM
                          && gReg.structImplements(nameOf(e.structName), intern("Display"));
            if (isVal) {
                data: long = 0;
                // A named scalar's `&self` is the integer itself, as `Lowerer.boxAny` hands it.
                if (namedScalar(e.kind, e.structName)) { data = self.eval(a, arg).bits; }
                else { data = self.baseAddress(a, arg); }
                if (self.stopped) { return none; }
                self.storeBits(at, 8, 3);
                self.storeBits(at + 8, 8, data);
                self.storeBits(at + 16, 8, self.methodTable(e.structName, intern("Display")));
            } else if (isObj) {
                obj: long = self.place(a, arg);
                if (self.stopped) { return none; }
                h: long = self.loadWord(obj + 8);
                if (h < VT_BASE || h - VT_BASE >= self.vtConcrete.len()) { return self.stop(stringOf("a `Display` object with no vtable")); }
                self.storeBits(at, 8, 3);
                self.storeBits(at + 8, 8, self.loadWord(obj));
                self.storeBits(at + 16, 8, self.methodTable(self.vtConcrete.get(h - VT_BASE), self.vtTrait.get(h - VT_BASE)));
            } else if (e.kind == Lit.Str) {
                v: CtValue = self.eval(a, arg);
                if (self.stopped) { return none; }
                self.storeBits(at, 8, 2);
                self.storeBits(at + 8, 8, self.loadWord(v.bits));
                self.storeBits(at + 16, 8, self.loadWord(v.bits + 8));
            } else {
                v: CtValue = self.eval(a, arg);
                if (self.stopped) { return none; }
                tag: long = 0;                                 // int, bool, and the narrower ones
                if (e.kind == Lit.Char) { tag = 4; }
                else if (e.kind == Lit.Long) { tag = 1; }
                else if (e.kind == Lit.U64 || e.kind == Lit.Ptr) { tag = 5; }
                else if (e.kind == Lit.Double) { tag = 6; }
                else if (e.kind == Lit.Float) { tag = 7; }
                else if (isTruthValue(e.kind, e.op)) { tag = boxTagOf("Bool", 0); }
                // A float's box: the formatter's handle in `y`, as `Lowerer.boxAny` puts its address.
                y: long = 0;
                if ((tag == 6 || tag == 7) && gFloatBoxFormat != NO_SYM) {
                    hit: Option<long> = self.fnAt.find(gFloatBoxFormat as long);
                    match hit { Some(i) { y = FN_BASE + i; } None { } }
                }
                self.storeBits(at, 8, tag);
                self.storeBits(at + 8, 8, v.bits);
                self.storeBits(at + 16, 8, y);
            }
            if (self.stopped) { return none; }
        }
        pair: long = self.alloc(16);
        self.storeBits(pair, 8, buf);
        self.storeBits(pair + 8, 8, n);
        return CtValue { kind: Lit.Slice, structName: p.structName, bits: pair };
    }

    // Lays out a vtable in memory for code that reads one as words (`fmt.k`'s `callDisplay` loads
    // slot 0 and calls it): each method's handle, in the trait's order. A trait object's own
    // vtable is a handle that dispatch decodes (`vtableHandle`), which code reading words cannot
    // follow. The table goes in the caller's frame, since the call it is built for runs inside it.
    methodTable &self concrete:Sym trait:Sym -> long {
        ii: long = gReg.findImplMangled(concrete, trait);
        if (ii < 0) { self.stop(format("`{}` as `{}`, which nothing implements", nameOf(concrete), nameOf(trait))); return 0; }
        im: TraitImplDef = gReg.implAt(ii);
        ti: long = gReg.findTraitSym(im.trait.name);
        if (ti < 0) { self.stop(format("a trait it cannot find, `{}`", nameOf(trait))); return 0; }
        t: TraitDef = gReg.traitDef(ti);
        tab: long = self.alloc(8 * t.methodCount + 8);
        for k in 0..t.methodCount {
            m: Sym = implMethodName(im, gReg.traitMethodAt(t, k).name);
            hit: Option<long> = self.fnAt.find(m as long);
            h: long = 0;
            match hit { Some(i) { h = FN_BASE + i; } None { } }
            self.storeBits(tab + 8 * k, 8, h);
        }
        return tab;
    }

    invokeWithSelf &self inout a:Ast at:long selfAddr:long nodes:Vec<NodeId> -> CtValue {
        none: CtValue = CtValue { kind: Lit.Void, structName: NO_SYM, bits: 0 };
        f: FnNode = a.fns.get(at);
        if (f.argCount != nodes.len() + 1) { return self.stop(format("a dispatch to `{}` with the wrong number of arguments", nameOf(f.name))); }
        vals: Vec<CtValue>;
        p0: VarDeclNode = a.paramAt(f, 0);
        vals.push(CtValue { kind: Lit.Ref, structName: p0.structName, bits: selfAddr });
        for k in 0..nodes.len() {
            vals.push(self.argValue(a, a.paramAt(f, k + 1), nodes.get(k)));
            if (self.stopped) { return none; }
        }
        return self.run(a, at, vals);
    }
    // Evaluates an argument in the caller's frame: an address for a borrow of an aggregate or
    // for an array, and a value for anything else. An aggregate's value is its address, and it is
    // copied once the callee's frame exists. A borrow of a scalar is not an address; see
    // `refToScalar`.
    argValue &self inout a:Ast p:VarDeclNode n:NodeId -> CtValue {
        none: CtValue = CtValue { kind: Lit.Void, structName: NO_SYM, bits: 0 };
        if (p.isVariadic) { return self.stop(format("a call that passes a variadic (`{}`)", nameOf(p.name))); }
        if (p.kind == Lit.Ref && !p.isArray && !refToScalar(p.structName)) {
            // An address handed over as a number or a raw pointer is the address the borrow is.
            // That happens in a call through a fn value typed `fn(long, ...)`, which is how
            // `fmt.k`'s `callDisplay` calls a `display &self`: at runtime the register holds the
            // address, so here the value does.
            ak: Lit = a.expr(n).kind;
            if (ak == Lit.Long || ak == Lit.Ptr || ak == Lit.U64) {
                return CtValue { kind: Lit.Ref, structName: p.structName, bits: self.eval(a, n).bits };
            }
            return CtValue { kind: Lit.Ref, structName: p.structName, bits: self.baseAddress(a, n) };
        }
        if (p.isArray) { return CtValue { kind: p.kind, structName: p.structName, bits: self.place(a, n) }; }
        return self.eval(a, n);
    }
    run &self inout a:Ast at:long vals:Vec<CtValue> -> CtValue {
        none: CtValue = CtValue { kind: Lit.Void, structName: NO_SYM, bits: 0 };
        f: FnNode = a.fns.get(at);
        // A dependency's body is only typed if this compile checked it for exactly this; one the
        // walk from the macros and initializers did not reach is a body nobody vouched for.
        if (isUnchecked(at)) {
            return self.stop(format("a call to `{}`, a dependency's function this package did not prepare to run at compile time", nameOf(f.name)));
        }
        ret: long = 0;
        aggRet: bool = f.returnKind != Lit.Void && f.returnKind != Lit.Ref && f.returnKind != Lit.Ptr
                       && f.returnKind != Lit.Fn && !ctScalar(f.returnKind, f.returnStruct);
        if (aggRet) { ret = self.alloc(typeBytes(f.returnKind, f.returnStruct)); }
        self.pushFrame();
        for k in 0..vals.len() {
            p: VarDeclNode = a.paramAt(f, k);
            slot: long = self.declare(p);
            v: CtValue = vals.get(k);
            if (p.isArray) { self.copy(slot, v.bits, declaredBytesOf(p)); }
            else { self.assignTo(slot, p.kind, p.structName, v); }
            if (self.stopped) { self.popFrame(); return none; }
        }
        self.execBlock(a, f.body);
        result: CtValue = none;
        if (!self.stopped) {
            if (self.returning) {
                self.returning = false;
                if (aggRet) {
                    rv: CtValue = self.retVal;
                    if (rv.kind == Lit.Struct && f.returnKind == Lit.TraitObj) {
                        self.assignTo(ret, Lit.TraitObj, f.returnStruct, rv);
                    } else {
                        self.copy(ret, rv.bits, typeBytes(f.returnKind, f.returnStruct));
                    }
                    result = CtValue { kind: f.returnKind, structName: f.returnStruct, bits: ret };
                } else if (f.returnKind == Lit.Void) {
                    result = none;
                } else if (ctScalar(f.returnKind, f.returnStruct)) {
                    result = make(f.returnKind, f.returnStruct, self.retVal.bits);
                } else {
                    result = CtValue { kind: f.returnKind, structName: f.returnStruct, bits: self.retVal.bits };
                }
            } else if (f.returnKind != Lit.Void) {
                self.stop(format("the end of `{}` without a `return`", nameOf(f.name)));
            }
        }
        self.popFrame();
        if (self.stopped) { return none; }
        return result;
    }

    // ─── statements ──────────────────────────────────────────────────────────

    // Runs a block's statements until one leaves it: a return, a break, a continue, a refusal.
    execBlock &self inout a:Ast b:long -> void {
        // There is nothing to run when the body is in another object, and a fold that reaches
        // one cannot finish. `Evaluator::call` refuses such a call before it gets here; this is
        // only the backstop.
        if (b < 0) { return; }
        n: long = a.blockLen(b);
        for k in 0..n {
            self.curBlock = b;
            self.curAt = k;
            self.exec(a, a.stmtAt(b, k));
            if (self.stopped || self.returning || self.breaking || self.continuing) { return; }
        }
    }

    exec &self inout a:Ast st:Stmt -> void {
        if (!self.tick()) { return; }
        if (st.kind == StmtKind.VarDecl) {
            d: VarDeclNode = a.decls.get(st.at);
            if (d.init == NO_NODE) { self.declare(d); return; }
            // The initializer runs first, in the frame as it is. A struct literal or a call
            // builds a temporary, and the new local is a copy of it. That is the only way a
            // declaration differs from an assignment: which storage is fresh.
            v: CtValue = self.eval(a, d.init);
            if (self.stopped) { return; }
            slot: long = self.declare(d);
            if (d.isArray) { self.copy(slot, self.arrayFrom(a, d.init, v), declaredBytesOf(d)); }
            else { self.assignTo(slot, d.kind, d.structName, v); }
            return;
        }
        if (st.kind == StmtKind.Expr || st.kind == StmtKind.Call) {
            v: NodeId = a.exprStmts.get(st.at).value;
            if (self.forElement(a, v)) { return; }
            if (self.macroRun && self.bindBorrow(a, v)) { return; }
            self.eval(a, v);
            return;
        }
        if (st.kind == StmtKind.Return) {
            r: ReturnNode = a.returns.get(st.at);
            v: CtValue = CtValue { kind: Lit.Void, structName: NO_SYM, bits: 0 };
            if (r.value != NO_NODE) { v = self.eval(a, r.value); }
            if (self.stopped) { return; }
            self.retVal = v;
            self.returning = true;
            return;
        }
        if (st.kind == StmtKind.If) {
            at: long = st.at;
            while (at >= 0) {
                br: IfNode = a.ifs.get(at);
                c: CtValue = self.eval(a, br.cond);
                if (self.stopped) { return; }
                if (c.bits != 0) { self.execBlock(a, br.body); return; }
                at = br.elseIf;
            }
            return;
        }
        if (st.kind == StmtKind.While) {
            w: WhileNode = a.whiles.get(st.at);
            while (true) {
                c: CtValue = self.eval(a, w.cond);
                if (self.stopped) { return; }
                if (c.bits == 0) { return; }
                self.execBlock(a, w.body);
                if (self.stopped || self.returning) { return; }
                self.continuing = false;
                if (self.breaking) { self.breaking = false; return; }
                if (w.step >= 0) {
                    self.execBlock(a, w.step);
                    if (self.stopped || self.returning) { return; }
                }
            }
        }
        if (st.kind == StmtKind.Loop) {
            body: long = a.blockStmts.get(st.at).body;
            while (true) {
                self.execBlock(a, body);
                if (self.stopped || self.returning) { return; }
                self.continuing = false;
                if (self.breaking) { self.breaking = false; return; }
            }
        }
        // An `unsafe` block grants the program raw pointers; here every access is bounds-checked
        // whatever the source says, and what is refused inside one is refused on its own account.
        if (st.kind == StmtKind.Block || st.kind == StmtKind.Unsafe) { self.execBlock(a, a.blockStmts.get(st.at).body); return; }
        if (st.kind == StmtKind.Break)    { self.breaking = true; return; }
        if (st.kind == StmtKind.Continue) { self.continuing = true; return; }
        // The arms carry their own tests, built by the parser, and their bindings as ordinary
        // declarations; the last arm is reached by elimination.
        if (st.kind == StmtKind.Match) {
            m: MatchNode = a.matches.get(st.at);
            for k in 0..m.armCount {
                arm: ArmNode = a.arms.get(m.firstArm + k);
                if (arm.test == NO_NODE) { self.execBlock(a, arm.body); return; }
                c: CtValue = self.eval(a, arm.test);
                if (self.stopped) { return; }
                if (c.bits != 0) { self.execBlock(a, arm.body); return; }
            }
            return;
        }
        if (st.kind == StmtKind.Asm)   { self.stop(stringOf("an `asm` block")); return; }
        if (st.kind == StmtKind.With)  { self.stop(stringOf("a `with` block")); return; }
        if (st.kind == StmtKind.Recover) { self.stop(stringOf("a `recover` statement")); return; }
        self.stop(stringOf("a statement it does not run yet"));
    }
}

// ─── the value model ─────────────────────────────────────────────────────────

// What `p + 1` moves by: the pointee's width for a typed pointer, one byte for a raw address
// (a `.ptr` read out of a `str` or a slice, whose companion the lowerer strips too).
local strideOf n:Sym -> long {
    if (n == NO_SYM) { return 1; }
    return namedWidth(n);
}

pub isVarGlobal n:Sym -> bool {
    gi: long = gReg.findGlobalSym(n);
    if (gi < 0) { return true; }
    return gReg.globalDef(gi).isVar;
}

// What holds a number: an integer of any width, a bool, or a backed enum, which is one.
// A borrow of a scalar is the scalar: `methods long for Hash` writes `hash &self`, so `self` is
// typed `ref_long` and the one word held there is the value rather than an address.
// `Lowerer::lowerArg` passes an argument by its own kind for this reason, and `long_hash` converts
// that word straight to `u64` with no load. Only an aggregate's borrow is a real address.
local refToScalar n:Sym -> bool {
    if (n == NO_SYM) { return false; }
    if (gReg.findStructSym(n) >= 0) { return false; }     // a struct: the borrow is its address
    if (namedScalar(Lit.Struct, n)) { return true; }      // a backed enum is its backing integer
    return namesScalar(nameOf(n));
}

pub ctScalar k:Lit n:Sym -> bool {
    s: Lit = storedKind(k, n);
    return isInteger(s) || s == Lit.Bool || isFloat(s);
}

// The left of `-x` over a float: the parser's zero, which the checker gave the float's type. A
// float literal written in the source keeps its spelling (`Text`); the parser marked this one.
pub isNegationMark e:Expr -> bool {
    if (e.op != Op.Literal || !isFloat(e.kind) || !e.isParen) { return false; }
    p: Payload = e.payload;
    match p { Num(v) { return true; } _ { } }
    return false;
}

// `x as T` on bits: between a float and anything numeric the value converts, the way the
// emitted `cvt` instruction does it; everything else is the bits, re-extended by `make`.
pub convertBits v:long from:Lit to:Lit -> long {
    if (from == to) { return v; }
    if (from == Lit.Double) {
        if (to == Lit.Float) { return f64ToF32(v); }
        if (to == Lit.U64) { return f64ToU64(v); }
        if (isInteger(to) || to == Lit.Bool) { return f64ToI64(v); }
        return v;
    }
    if (from == Lit.Float) {
        if (to == Lit.Double) { return f32ToF64(v); }
        if (to == Lit.U64) { return f32ToU64(v); }
        if (isInteger(to) || to == Lit.Bool) { return f32ToI64(v); }
        return v;
    }
    if (to == Lit.Double) { if (from == Lit.U64) { return u64ToF64(v); } return i64ToF64(v); }
    if (to == Lit.Float) { if (from == Lit.U64) { return u64ToF32(v); } return i64ToF32(v); }
    return v;
}

// `v` at the width and signedness of `t`: sign- or zero-extended from `t`'s own bytes, exactly as
// a load of that type does on the machine. A bool is 0 or 1.
pub wrapTo v:long t:Lit -> long {
    if (t == Lit.Bool) { return boolBits(v != 0); }
    size: long = typeInfo(t).size;
    if (size >= 8 || size < 1) { return v; }
    bits: long = size * 8;
    mask: long = (1 << bits) - 1;
    low: long = v & mask;
    if (isUnsignedInt(t)) { return low; }
    if ((low & (1 << (bits - 1))) != 0) { return low - (1 << bits); }
    return low;
}
local make k:Lit n:Sym v:long -> CtValue { return CtValue { kind: k, structName: n, bits: wrapTo(v, storedKind(k, n)) }; }
local boolBits b:bool -> long { if (b) { return 1; } return 0; }

// The storage a declaration needs. This is `declaredBytes` as the lowerer computes it for the
// same declaration, so a compile-time slot is exactly the size of the runtime one.
pub declaredBytesOf d:VarDeclNode -> long {
    unit: long = typeBytes(d.kind, d.structName);
    if (d.isArray) { return unit * d.count; }
    if (d.kind == Lit.Ref || d.kind == Lit.Ptr || d.kind == Lit.Fn) { return 8; }
    if (unit < 8) { return 8; }
    return unit;
}

// ─── effects ─────────────────────────────────────────────────────────────────
//
// Which globals a piece of runtime code may write. A global's initializer that did not fold
// still runs at startup, before the initializers after it, so a later one may be folded only if
// nothing that earlier code can reach writes the globals it reads. That is a question about the
// call graph, and it is answered here. Each function's own effects are scanned once: the globals
// it assigns, lends with `&` or calls a method on, and whether it does anything opaque (a store
// through a pointer, a call with no known target), which counts as writing everything. The set
// only grows as initializers are added, so every function is visited at most once over the
// whole fold.

methods Effects for Default {
    new -> Effects {
        return Effects { all: false, written: map![], order: vec![], visited: vec![], fnAt: map![] };
    }
}

methods Effects {
    reset &self inout a:Ast -> void {
        self.all = false;
        self.written.clear();
        self.order.clear();
        self.visited.clear();
        for i in 0..a.fns.len() { self.visited.push(false); }
        self.fnAt.clear();
        for i in 0..a.fns.len() {
            f: FnNode = a.fns.get(i);
            if (!f.isTemplate) { self.fnAt.put(f.name as long, i); }
        }
    }

    mark &self g:Sym -> void {
        if (self.written.has(nameOf(g))) { return; }
        self.written.put(nameOf(g), 1);
        self.order.push(g);
    }

    mayWrite &self g:Sym -> bool {
        if (self.all) { return true; }
        return self.written.has(nameOf(g));
    }

    // Everything the expression can reach: its own writes, and every callee's, transitively.
    addExpr &self inout a:Ast id:NodeId -> void {
        if (self.all || id == NO_NODE) { return; }
        e: Expr = a.expr(id);
        if (e.op == Op.Assignment) {
            self.noteTarget(a, e.left);
            self.addExpr(a, e.right);
            return;
        }
        if (e.left != NO_NODE) { self.addExpr(a, e.left); self.addExpr(a, e.right); return; }
        if (e.op == Op.AddressOf) {
            match e.payload { Sub(v) { self.noteTarget(a, v); } _ { } }
            return;
        }
        if (e.op == Op.FunctionCall || e.op == Op.MethodCall) {
            c: CallNode = a.calls.get(0);
            match e.payload { Call(i) { c = a.calls.get(i); } _ { } }
            for k in 0..c.argCount { self.addExpr(a, a.argAt(c, k)); }
            if (c.receiver != NO_NODE) {
                // A method may write its receiver, and this one's callee is resolved by the
                // receiver's type, which is what the resolved name already carries.
                self.noteTarget(a, c.receiver);
                self.addExpr(a, c.receiver);
            }
            if (c.callee != NO_NODE || c.slot != NO_SLOT) { self.all = true; return; }
            self.addFunction(a, c.name);
            return;
        }
        match e.payload {
            Sub(v)   { self.addExpr(a, v); }
            Field(i) { self.addExpr(a, a.fields.get(i).base); }
            Index(i) {
                ix: IndexNode = a.indexes.get(i);
                self.addExpr(a, ix.base); self.addExpr(a, ix.index);
                self.addExpr(a, ix.sliceStart); self.addExpr(a, ix.sliceEnd);
            }
            Lit(i) {
                l: LitNode = a.lits.get(i);
                for k in 0..l.initCount { self.addExpr(a, a.inits.get(l.firstInit + k).value); }
                self.addExpr(a, l.rest);
            }
            _ { }
        }
    }

    // The place an assignment, a borrow or a method call reaches: the variable at the base of
    // the chain. A global there is written; a store through a pointer could reach anything.
    noteTarget &self inout a:Ast id:NodeId -> void {
        at: NodeId = id;
        while (at != NO_NODE) {
            e: Expr = a.expr(at);
            if (e.op == Op.Lvalue) {
                match e.payload {
                    Name(n) { if (gReg.findGlobalSym(n) >= 0) { self.mark(n); } }
                    _ { }
                }
                return;
            }
            if (e.op == Op.Deref) { self.all = true; return; }
            next: NodeId = NO_NODE;
            match e.payload {
                Field(i) { next = a.fields.get(i).base; }
                Index(i) {
                    ix: IndexNode = a.indexes.get(i);
                    next = ix.base;
                    if (next == NO_NODE && gReg.findGlobalSym(ix.name) >= 0) { self.mark(ix.name); }
                }
                Sub(v) { next = v; }
                _ { }
            }
            at = next;
        }
    }

    addFunction &self inout a:Ast name:Sym -> void {
        hit: Option<long> = self.fnAt.find(name as long);
        at: long = -1;
        match hit { Some(i) { at = i; } None { } }
        // No body to read. A syscall wrapper's `asm` sits inside a body the program does have, so
        // a name the program does not define is something outside it entirely: assume the worst.
        if (at < 0) { self.all = true; return; }
        // A dependency's body that was not checked here: its writes are unknown, so assume all.
        if (isUnchecked(at)) { self.all = true; return; }
        if (self.visited.get(at)) { return; }
        self.visited.set(at, true);
        self.addBlock(a, a.fns.get(at).body);
    }

    addBlock &self inout a:Ast b:long -> void {
        if (b < 0) { return; }
        n: long = a.blockLen(b);
        k: long = 0;
        while (k < n && !self.all) {
            self.addStmt(a, a.stmtAt(b, k));
            k = k + 1;
        }
    }

    addStmt &self inout a:Ast st:Stmt -> void {
        if (st.kind == StmtKind.VarDecl) { self.addExpr(a, a.decls.get(st.at).init); return; }
        if (st.kind == StmtKind.Expr || st.kind == StmtKind.Call) { self.addExpr(a, a.exprStmts.get(st.at).value); return; }
        if (st.kind == StmtKind.Return) { self.addExpr(a, a.returns.get(st.at).value); return; }
        if (st.kind == StmtKind.If) {
            at: long = st.at;
            while (at >= 0) {
                br: IfNode = a.ifs.get(at);
                self.addExpr(a, br.cond);
                self.addBlock(a, br.body);
                at = br.elseIf;
            }
            return;
        }
        if (st.kind == StmtKind.While || st.kind == StmtKind.Recover) {
            w: WhileNode = a.whiles.get(st.at);
            self.addExpr(a, w.cond);
            self.addBlock(a, w.body);
            self.addBlock(a, w.step);
            return;
        }
        if (st.kind == StmtKind.Loop || st.kind == StmtKind.Block || st.kind == StmtKind.Unsafe) {
            self.addBlock(a, a.blockStmts.get(st.at).body);
            return;
        }
        if (st.kind == StmtKind.Match) {
            m: MatchNode = a.matches.get(st.at);
            for k in 0..m.armCount { self.addBlock(a, a.arms.get(m.firstArm + k).body); }
            return;
        }
        if (st.kind == StmtKind.With) {
            w: WithNode = a.withs.get(st.at);
            if (gReg.findGlobalSym(w.name) >= 0) { self.mark(w.name); }
            self.addBlock(a, w.body);
            return;
        }
        if (st.kind == StmtKind.Destructure) { self.addExpr(a, a.destructures.get(st.at).value); return; }
        if (st.kind == StmtKind.Break || st.kind == StmtKind.Continue || st.kind == StmtKind.StructDecl
            || st.kind == StmtKind.FunctionDef) { return; }
        // An `asm` block reaches a program global in only two ways: an `out` naming it, or a line
        // of text spelling its `gbl_` symbol. Its `in` expressions are ordinary expressions (so a
        // `&g` among them counts as a write of `g`, like any other borrow), and whatever else the
        // text touches (the allocator's own labels, a syscall) is not a program global.
        if (st.kind == StmtKind.Asm) {
            n: AsmNode = a.asms.get(st.at);
            for k in 0..n.pieceCount {
                pc: AsmPiece = a.asmPieces.get(n.firstPiece + k);
                if (pc.kind == AsmKind.In) { self.addExpr(a, pc.value); }
                if (pc.kind == AsmKind.Out && gReg.findGlobalSym(pc.name) >= 0) { self.mark(pc.name); }
                if (pc.kind == AsmKind.Text && strContains(nameOf(pc.text), "gbl_")) { self.all = true; }
            }
            return;
        }
        self.all = true;
    }
}

// ─── macros ──────────────────────────────────────────────────────────────────
//
// A macro is a function the compiler runs while checking. The checker hands over the callee and
// its arguments, each already a value in this evaluator's memory (a `Node` built by quoting the
// caller's argument tree, or a constant), and takes back the result: a scalar, or a `Node` that
// `spliceExpr`/`spliceStmt` turn back into syntax. Turning it back walks the `Node` value by
// `stdlib::ast`'s own layout, exactly as promotion walks any struct, so the evaluator knows
// nothing about the tree's shape beyond the variant names.
//
// Hygiene: a name the spliced code declares (`Let`) is given a fresh name that no source can
// spell, and every mention of it inside the same splice follows. Every other name resolves where
// the splice lands, which is how a quoted `panic(...)` finds `panic` and a quoted argument finds
// the caller's variable.

methods Evaluator {
    // Runs function `at` on `vals` as a macro, over the globals snapshot `beginMacro` laid out.
    // Frames from any previous run are gone; the literal segment and the heap persist, and a
    // `Node` the caller built for an argument stays where it is.
    runMacro &self inout a:Ast page:long at:long vals:Vec<CtValue> -> CtValue {
        self.indexFunctions(a, page);
        if (self.mem.len() == 0) { self.alloc(16); self.globalsEnd = self.mem.len(); }
        self.names.clear(); self.slots.clear(); self.kinds.clear(); self.snames.clear();
        self.arrays.clear(); self.counts.clear(); self.aliased.clear();
        self.frameBase.clear(); self.frameBase.push(0);
        self.frameSp.clear(); self.frameSp.push(self.mem.len());
        self.steps = 0;
        self.offsets.clear();             // layouts may have settled since (`fieldOffset`)
        self.stopped = false;
        self.refusal.clear();
        self.refused = false;
        self.ctErr.clear();
        self.returning = false; self.breaking = false; self.continuing = false;
        // The arguments live in the caller's part of the stack; a frame pop must not take them.
        self.frameSp.set(0, self.mem.len());
        return self.run(a, at, vals);
    }

    // Lays out the globals as a macro sees them, before its arguments are built. This is a
    // snapshot: a global with a literal initializer holds its value, and any other is zero until
    // something reads it. A macro's writes land in the snapshot and go away with the run, which
    // is what a table filled on first use wants, and which keeps a macro's write to a global from
    // becoming a startup effect the program never sees.
    //
    // The snapshot is the same for every run on one page, so it is built once and copied. An
    // initializer that was not a literal when it was built is evaluated on first read
    // (`globalPlace`) from whatever it is now, which is what laying it out again would have found.
    beginMacro &self inout a:Ast page:long -> void {
        self.indexFunctions(a, page);
        self.extReady.clear();
        if (page == self.macroPage && a.blockLen(page) == self.macroPageLen) {
            self.mem.clear();
            unsafe { self.mem.extendSlice(self.macroImage.buf.ptr[0..self.macroImage.len()]); }
            self.folded.clear();
            for k in 0..self.macroFolded.len() { self.folded.push(self.macroFolded.get(k)); }
            self.globalsEnd = self.mem.len();
            self.macroRun = true;
            return;
        }
        self.mem.clear();
        self.alloc(16);
        self.globalAddr.clear();
        self.gNames.clear(); self.gStarts.clear(); self.gDecls.clear(); self.folded.clear();
        n: long = a.blockLen(page);
        for k in 0..n {
            st: Stmt = a.stmtAt(page, k);
            if (st.kind == StmtKind.VarDecl) {
                d: VarDeclNode = a.decls.get(st.at);
                addr: long = self.alloc(declaredBytesOf(d));
                self.globalAddr.put(nameOf(d.name), addr);
                self.gNames.push(d.name); self.gStarts.push(addr); self.gDecls.push(st.at);
                self.folded.push(d.init == NO_NODE);
                if (d.init != NO_NODE && !d.isArray && ctScalar(d.kind, d.structName)) {
                    e: Expr = a.expr(d.init);
                    if (e.op == Op.Literal) {
                        self.committing = true;
                        self.storeLiteral(addr, d, e);
                        self.committing = false;
                        self.folded.set(self.folded.len() - 1, true);
                    }
                }
            }
        }
        self.globalsEnd = self.mem.len();
        self.macroRun = true;
        self.macroImage.clear();
        unsafe { self.macroImage.extendSlice(self.mem.buf.ptr[0..self.mem.len()]); }
        self.macroFolded.clear();
        for k in 0..self.folded.len() { self.macroFolded.push(self.folded.get(k)); }
        self.macroPage = page;
        self.macroPageLen = a.blockLen(page);
    }
    // Evaluates one expression on its own (a macro argument) in a fresh frame that is never
    // popped, so the value it built (a `Node` on the stack) stays for the macro to read.
    evalExpr &self inout a:Ast page:long id:NodeId -> CtValue {
        self.indexFunctions(a, page);
        if (self.mem.len() == 0) { self.alloc(16); self.globalsEnd = self.mem.len(); }
        self.names.clear(); self.slots.clear(); self.kinds.clear(); self.snames.clear();
        self.arrays.clear(); self.counts.clear(); self.aliased.clear();
        self.frameBase.clear(); self.frameBase.push(0);
        self.frameSp.clear(); self.frameSp.push(self.mem.len());
        self.steps = 0;
        self.offsets.clear();             // layouts may have settled since (`fieldOffset`)
        self.stopped = false;
        self.refusal.clear();
        self.returning = false; self.breaking = false; self.continuing = false;
        return self.eval(a, id);
    }

    // ─── source -> Node: the parser as a macro sees it ───────────────────────

    // A `str` pair in evaluator memory holds a piece of source: parse it as one expression, in
    // the module the macro call was written in, and build the tree as a Node value on the heap.
    parseSnippet &self pair:long -> long {
        p: long = self.loadWord(pair);
        n: long = self.loadWord(pair + 8);
        // A `#file` marker first, so a name qualifies to the caller's module.
        text: String;
        text.pushStr("#file ");
        text.push(34 as char);
        if (self.macroFile != NO_SYM) { text.pushStr(nameOf(self.macroFile)); } else { text.pushStr("<macro>"); }
        text.push(34 as char);
        text.pushStr(" 1 ");
        text.push(34 as char);
        if (self.macroPkg != NO_SYM) { text.pushStr(nameOf(self.macroPkg)); }
        text.push(34 as char);
        text.push(10 as char);
        for i in 0..n { text.push(self.byteAt(p + i) as char); }
        if (self.stopped) { return 0; }
        ps: Parser = parserOf(keepString(text));
        id: NodeId = ps.parseExpr();
        if (!ps.check(Tok.FileEnd)) {
            failStr(format("unexpected `{}` after the expression given to `parseExpr`\nnote: `parseExpr` reads exactly one expression", tokName(ps.cur.kind)));
        }
        return self.nodeValueOf(&ps.ast, id);
    }

    // A fresh Node on the compile-time heap, tagged.
    newNode &self variant:str -> long {
        d: StructDef = gReg.structDef(gReg.findStructSym(self.nodeSym));
        ed: EnumDef = gReg.enumDef(gReg.findEnumSym(self.nodeSym));
        addr: long = self.ctMalloc(d.size);
        self.store(addr, ed.backing, NO_SYM, gReg.variantAt(ed, gReg.findVariant(ed, variant)).value);
        return addr;
    }
    // Whether the library's Node declares a variant of this name.
    nodeHas &self variant:str -> bool {
        ei: long = gReg.findEnumSym(self.nodeSym);
        if (ei < 0) { return false; }
        return gReg.findVariant(gReg.enumDef(ei), variant) >= 0;
    }
    // A `BinOp`/`UnOp` constant, by its name in the enum.
    opTag &self owner:str name:str -> long {
        ed: EnumDef = gReg.enumDef(gReg.findEnum(owner));
        vi: long = gReg.findVariant(ed, name);
        if (vi < 0) { failStr(format("no variant `{}` in enum `{}`", name, owner)); }
        return gReg.variantAt(ed, vi).value;
    }
    // A `str` payload: the bytes copied to the heap, the pair written at `at`.
    putStr &self at:long text:str -> void {
        b: long = self.ctMalloc(text.len);
        for i in 0..text.len { self.rawSet(b + i, charAt(text, i) as u8); }
        self.storeBits(at, 8, b);
        self.storeBits(at + 8, 8, text.len);
    }
    // A `Box<Node>` payload: a heap copy of the node, its address written at `at`.
    putBox &self at:long node:long -> void {
        w: long = typeBytes(Lit.Struct, self.nodeSym);
        b: long = self.ctMalloc(w);
        self.copy(b, node, w);
        self.storeBits(at, 8, b);
    }
    // A `Vec<Node>` or `Vec<str>` payload: a block of the elements, and the header written at
    // `at` by the instance's own layout (`buf` is a `RawVec {ptr, cap}`, followed by `count`).
    putVec &self at:long sname:Sym buf:long n:long -> void {
        d: StructDef = gReg.structDef(gReg.findStructSym(sname));
        bf: FieldDef = gReg.fieldAt(d, gReg.findField(d, "buf"));
        cf: FieldDef = gReg.fieldAt(d, gReg.findField(d, "count"));
        self.storeBits(at + bf.offset, 8, buf);
        self.storeBits(at + bf.offset + 8, 8, n);
        self.storeBits(at + cf.offset, 8, n);
    }
    putNodeVec &self at:long sname:Sym items:Vec<long> -> void {
        w: long = typeBytes(Lit.Struct, self.nodeSym);
        n: long = items.len();
        buf: long = 0;
        if (n > 0) {
            buf = self.ctMalloc(n * w);
            for i in 0..n { self.copy(buf + i * w, items.get(i), w); }
        }
        self.putVec(at, sname, buf, n);
    }
    putStrVec &self at:long sname:Sym items:Vec<Sym> -> void {
        n: long = items.len();
        buf: long = 0;
        if (n > 0) {
            buf = self.ctMalloc(n * 16);
            for i in 0..n { self.putStr(buf + i * 16, nameOf(items.get(i))); }
        }
        self.putVec(at, sname, buf, n);
    }

    // An expression of a freshly parsed tree as a Node value: the inverse of `spliceExpr`, over
    // the shapes the quoter serializes.
    nodeValueOf &self inout pa:Ast id:NodeId -> long {
        e: Expr = pa.expr(id);
        if (e.left != NO_NODE) {
            bn: str = binOpName(e.op);
            if (bn.len == 0) { failStr(format("`parseExpr` does not support this expression (operator {})", e.op as long)); }
            nd: long = self.newNode("Binary");
            self.store(nd + self.payload("Binary", 0).offset, Lit.Int, NO_SYM, self.opTag("ast::BinOp", bn));
            self.putBox(nd + self.payload("Binary", 1).offset, self.nodeValueOf(pa, e.left));
            self.putBox(nd + self.payload("Binary", 2).offset, self.nodeValueOf(pa, e.right));
            return nd;
        }
        un: str = unOpName(e.op);
        if (e.op == Op.AddressOf) { un = "AddrOf"; }
        if (un.len > 0) {
            nd: long = self.newNode("Unary");
            self.store(nd + self.payload("Unary", 0).offset, Lit.Int, NO_SYM, self.opTag("ast::UnOp", un));
            match e.payload { Sub(v) { self.putBox(nd + self.payload("Unary", 1).offset, self.nodeValueOf(pa, v)); } _ { } }
            return nd;
        }
        if (e.op == Op.Literal) {
            // A float literal keeps its spelling, as the parser left it, in the Node variant
            // `Float(str)` when the library's Node has one. Read as an `Int`, it would become 0.
            match e.payload {
                Text(t) {
                    if (!self.nodeHas("Float")) {
                        failStr(format("`parseExpr` cannot pass on the float literal `{}`\nnote: `Node` in `stdlib::ast` has no `Float(str)` variant to carry it", nameOf(t)));
                    }
                    nd: long = self.newNode("Float");
                    self.putStr(nd + self.payload("Float", 0).offset, nameOf(t));
                    return nd;
                }
                _ { }
            }
            v: long = 0;
            match e.payload { Num(x) { v = x; } _ { } }
            nd: long = self.newNode("Int");
            self.store(nd + self.payload("Int", 0).offset, Lit.Long, NO_SYM, v);
            return nd;
        }
        if (e.op == Op.StringLit) {
            nd: long = self.newNode("Str");
            match e.payload { Text(t) { self.putStr(nd + self.payload("Str", 0).offset, nameOf(t)); } _ { } }
            return nd;
        }
        if (e.op == Op.Lvalue) {
            nd: long = self.newNode("Name");
            match e.payload { Name(nm) { self.putStr(nd + self.payload("Name", 0).offset, nameOf(nm)); } _ { } }
            return nd;
        }
        if (e.op == Op.Sizeof) {
            nd: long = self.newNode("Sizeof");
            t: Expr = pa.measuredOf(id);
            self.putStr(nd + self.payload("Sizeof", 0).offset, typeMangleName(t.kind, t.structName));
            return nd;
        }
        if (e.op == Op.Nameof) {
            nd: long = self.newNode("Nameof");
            self.putStr(nd + self.payload("Nameof", 0).offset, nameOf(e.structName));
            match e.payload { Sub(v) { self.putBox(nd + self.payload("Nameof", 1).offset, self.nodeValueOf(pa, v)); } _ { } }
            return nd;
        }
        if (e.op == Op.Cast) {
            nd: long = self.newNode("Cast");
            match e.payload { Sub(v) { self.putBox(nd + self.payload("Cast", 0).offset, self.nodeValueOf(pa, v)); } _ { } }
            self.putStr(nd + self.payload("Cast", 1).offset, typeMangleName(e.kind, e.structName));
            return nd;
        }
        if (e.op == Op.FunctionCall || e.op == Op.MethodCall) {
            c: CallNode = pa.calls.get(0);
            match e.payload { Call(i) { c = pa.calls.get(i); } _ { } }
            items: Vec<long>;
            for k in 0..c.argCount { items.push(self.nodeValueOf(pa, pa.argAt(c, k))); }
            if (e.op == Op.MethodCall) {
                nd: long = self.newNode("Method");
                self.putBox(nd + self.payload("Method", 0).offset, self.nodeValueOf(pa, c.receiver));
                self.putStr(nd + self.payload("Method", 1).offset, nameOf(c.name));
                f: FieldDef = self.payload("Method", 2);
                self.putNodeVec(nd + f.offset, f.structName, items);
                return nd;
            }
            nd: long = self.newNode("Call");
            self.putStr(nd + self.payload("Call", 0).offset, nameOf(c.name));
            f: FieldDef = self.payload("Call", 1);
            self.putNodeVec(nd + f.offset, f.structName, items);
            return nd;
        }
        if (e.op == Op.FieldAccess) {
            fn: FieldNode = pa.fields.get(0);
            match e.payload { Field(i) { fn = pa.fields.get(i); } _ { } }
            nd: long = self.newNode("Field");
            self.putBox(nd + self.payload("Field", 0).offset, self.nodeValueOf(pa, fn.base));
            self.putStr(nd + self.payload("Field", 1).offset, nameOf(fn.name));
            return nd;
        }
        if (e.op == Op.ArrayIndex) {
            ix: IndexNode = pa.indexes.get(0);
            match e.payload { Index(i) { ix = pa.indexes.get(i); } _ { } }
            if (ix.whole || ix.index == NO_NODE) { failStr(stringOf("`parseExpr` does not support slice expressions yet")); }
            base: long = 0;
            if (ix.base != NO_NODE) { base = self.nodeValueOf(pa, ix.base); }
            else { base = self.newNode("Name"); self.putStr(base + self.payload("Name", 0).offset, nameOf(ix.name)); }
            nd: long = self.newNode("Index");
            self.putBox(nd + self.payload("Index", 0).offset, base);
            self.putBox(nd + self.payload("Index", 1).offset, self.nodeValueOf(pa, ix.index));
            return nd;
        }
        if (e.op == Op.StructLit || e.op == Op.TupleLit) {
            l: LitNode = pa.lits.get(0);
            match e.payload { Lit(i) { l = pa.lits.get(i); } _ { } }
            if (l.rest != NO_NODE) { failStr(stringOf("`parseExpr` does not support `..rest` in a literal yet")); }
            names: Vec<Sym>;
            vals: Vec<long>;
            for k in 0..l.initCount {
                in: InitNode = pa.inits.get(l.firstInit + k);
                names.push(in.name);
                vals.push(self.nodeValueOf(pa, in.value));
            }
            if (e.op == Op.TupleLit) {
                nd: long = self.newNode("TupleLit");
                f: FieldDef = self.payload("TupleLit", 0);
                self.putNodeVec(nd + f.offset, f.structName, vals);
                return nd;
            }
            nd: long = self.newNode("StructLit");
            self.putStr(nd + self.payload("StructLit", 0).offset, nameOf(l.typeName));
            nf: FieldDef = self.payload("StructLit", 1);
            self.putStrVec(nd + nf.offset, nf.structName, names);
            vf: FieldDef = self.payload("StructLit", 2);
            self.putNodeVec(nd + vf.offset, vf.structName, vals);
            return nd;
        }
        failStr(format("`parseExpr` does not support this expression (operator {})", e.op as long));
        return 0;
    }

    // ─── Node -> syntax ──────────────────────────────────────────────────────

    // The variant a Node at `addr` holds, by name, and where its payloads start.
    nodeVariant &self addr:long -> str {
        ei: long = gReg.findEnumSym(self.nodeSym);
        ed: EnumDef = gReg.enumDef(ei);
        tag: long = self.load(addr, ed.backing, NO_SYM);
        for v in 0..ed.variantCount {
            vd: VariantDef = gReg.variantAt(ed, v);
            if (vd.value == tag) { return nameOf(vd.name); }
        }
        return "";
    }
    // Payload `k` of a variant: where it is inside the Node, and what it is.
    payload &self variant:str k:long -> FieldDef {
        d: StructDef = gReg.structDef(gReg.findStructSym(self.nodeSym));
        fi: long = gReg.findFieldSym(d, enumPayloadField(variant, k));
        return gReg.fieldAt(d, fi);
    }
    // A `str` payload's bytes, wherever they are, as a symbol.
    readStr &self addr:long -> Sym {
        p: long = self.loadWord(addr);
        n: long = self.loadWord(addr + 8);
        s: String;
        for i in 0..n { s.push(self.byteAt(p + i) as char); }
        return internString(s);
    }
    // A `Box<Node>` payload: the Node it holds.
    readBox &self addr:long -> long { return self.loadWord(addr); }
    // A `Vec<Node>` or `Vec<str>` payload: its buffer and count.
    vecBuf &self addr:long sname:Sym -> long {
        d: StructDef = gReg.structDef(gReg.findStructSym(sname));
        buf: FieldDef = gReg.fieldAt(d, gReg.findField(d, "buf"));
        return self.loadWord(addr + buf.offset);           // RawVec.ptr is its first word
    }
    vecCount &self addr:long sname:Sym -> long {
        d: StructDef = gReg.structDef(gReg.findStructSym(sname));
        c: FieldDef = gReg.fieldAt(d, gReg.findField(d, "count"));
        return self.loadWord(addr + c.offset);
    }

    // The fresh name a spliced declaration gets, and what a mention of it becomes.
    hygienic &self n:Sym -> Sym {
        hit: Option<Sym> = self.renames.find(nameOf(n));
        match hit { Some(r) { return r; } None { } }
        return n;
    }
    declareHygienic &self n:Sym -> Sym {
        fresh: Sym = internString(format("$m{}_{}", self.macroSeq, nameOf(n)));
        self.renames.put(nameOf(n), fresh);
        return fresh;
    }

    // An expression Node as syntax. Kinds are the parser's placeholders; the checker stamps them.
    spliceExpr &self inout a:Ast addr:long -> NodeId {
        v: str = self.nodeVariant(addr);
        if (v == "Int") {
            n: long = self.load(addr + self.payload(v, 0).offset, Lit.Long, NO_SYM);
            k: Lit = Lit.Long;
            if (n >= -2147483648 && n <= 2147483647) { k = Lit.Int; }
            return a.leaf(Op.Literal, Payload.Num(n), k);
        }
        if (v == "Str") { return a.leaf(Op.StringLit, Payload.Text(self.readStr(addr + self.payload(v, 0).offset)), Lit.Str); }
        // A float literal by its spelling: its width is settled where it is used, as a written one's.
        if (v == "Float") { return a.leaf(Op.Literal, Payload.Text(self.readStr(addr + self.payload(v, 0).offset)), Lit.Double); }
        if (v == "Name") { return a.leaf(Op.Lvalue, Payload.Name(self.hygienic(self.readStr(addr + self.payload(v, 0).offset))), Lit.Long); }
        if (v == "Sizeof") {
            t: TypeRef = unmangledType(nameOf(self.readStr(addr + self.payload(v, 0).offset)));
            return a.sizeofNode(t.base, t.name);
        }
        if (v == "Nameof") {
            en: Sym = self.readStr(addr + self.payload(v, 0).offset);
            inner: NodeId = self.spliceExpr(a, self.readBox(addr + self.payload(v, 1).offset));
            return a.leafOf(Op.Nameof, Payload.Sub(inner), Lit.Str, en);
        }
        if (v == "Binary") {
            op: long = self.load(addr + self.payload(v, 0).offset, Lit.Int, NO_SYM);
            l: NodeId = self.spliceExpr(a, self.readBox(addr + self.payload(v, 1).offset));
            r: NodeId = self.spliceExpr(a, self.readBox(addr + self.payload(v, 2).offset));
            // BinOp is declared in Op's order less the leading Assignment, which comes last.
            bop: Op = Op.Assignment;
            if (op < 18) { bop = (op + 1) as Op; }
            // A store a macro built is held to what a written one is (`Parser.refuseNonPlace`).
            if (bop == Op.Assignment && !isPlaceOp(a.expr(l).op)) {
                failStr(format("cannot assign to {}\nnote: a store needs a place: a local, a field, an element or `*p`", nonPlaceText(a, l)));
            }
            return a.binary(bop, l, r, Lit.Long);
        }
        if (v == "Unary") {
            op: long = self.load(addr + self.payload(v, 0).offset, Lit.Int, NO_SYM);
            e: NodeId = self.spliceExpr(a, self.readBox(addr + self.payload(v, 1).offset));
            if (op == 0) { return a.binary(Op.Subtraction, a.leaf(Op.Literal, Payload.Num(0), Lit.Int), e, Lit.Long); }
            if (op == 1) { return a.unary(Op.LogicalNot, e, Lit.Int); }
            if (op == 2) { return a.unary(Op.BitwiseNot, e, Lit.Long); }
            if (op == 3) { return a.unary(Op.Deref, e, Lit.Long); }
            return a.unary(Op.AddressOf, e, Lit.Long);
        }
        if (v == "Cast") {
            e: NodeId = self.spliceExpr(a, self.readBox(addr + self.payload(v, 0).offset));
            t: TypeRef = unmangledType(nameOf(self.readStr(addr + self.payload(v, 1).offset)));
            return a.addExpr(Expr { op: Op.Cast, left: NO_NODE, right: NO_NODE, kind: t.base,
                                    structName: t.name, isParen: false, payload: Payload.Sub(e) });
        }
        if (v == "Call" || v == "Method") {
            // `E.V(a)` built as a method call on the enum's name, which is what a quote of
            // `@(e).@(v)(a)` gives, means the variant it names, just as the parser reads it.
            if (v == "Method") {
                ra: long = self.readBox(addr + self.payload(v, 0).offset);
                if (self.nodeVariant(ra) == "Name") {
                    en: Sym = self.readStr(ra + self.payload("Name", 0).offset);
                    vn: Sym = self.readStr(addr + self.payload(v, 1).offset);
                    ei: long = gReg.findEnumSym(en);
                    if (ei >= 0 && gReg.enumDef(ei).hasPayload && gReg.findVariant(gReg.enumDef(ei), nameOf(vn)) >= 0) {
                        vargs: Vec<NodeId> = self.spliceList(a, addr + self.payload(v, 2).offset, self.payload(v, 2).structName);
                        return self.variantLit(a, en, vn, vargs);
                    }
                }
            }
            recv: NodeId = NO_NODE;
            k: long = 0;
            if (v == "Method") { recv = self.spliceExpr(a, self.readBox(addr + self.payload(v, 0).offset)); k = 1; }
            f: Sym = self.readStr(addr + self.payload(v, k).offset);
            args: Vec<NodeId> = self.spliceList(a, addr + self.payload(v, k + 1).offset, self.payload(v, k + 1).structName);
            n: long = args.len();
            first: long = a.addArgs(args);
            a.calls.push(CallNode { name: f, receiver: recv, firstArg: first, argCount: n,
                                    slot: NO_SLOT, callee: NO_NODE, sigKey: NO_SYM });
            if (v == "Method") { return a.leaf(Op.MethodCall, Payload.Call(a.calls.len() - 1), Lit.Void); }
            return a.leaf(Op.FunctionCall, Payload.Call(a.calls.len() - 1), Lit.Int);
        }
        if (v == "Field") {
            b: NodeId = self.spliceExpr(a, self.readBox(addr + self.payload(v, 0).offset));
            a.fields.push(FieldNode { base: b, name: self.readStr(addr + self.payload(v, 1).offset) });
            return a.leaf(Op.FieldAccess, Payload.Field(a.fields.len() - 1), Lit.Long);
        }
        if (v == "Index") {
            b: NodeId = self.spliceExpr(a, self.readBox(addr + self.payload(v, 0).offset));
            i: NodeId = self.spliceExpr(a, self.readBox(addr + self.payload(v, 1).offset));
            a.indexes.push(IndexNode { name: NO_SYM, base: b, index: i, whole: false, rawPointerBase: false,
                                       sliceStart: NO_NODE, sliceEnd: NO_NODE, at: NO_SYM });
            return a.leaf(Op.ArrayIndex, Payload.Index(a.indexes.len() - 1), Lit.Long);
        }
        if (v == "StructLit" || v == "TupleLit") {
            tname: Sym = NO_SYM;
            names: Vec<Sym>;
            k: long = 0;
            if (v == "StructLit") {
                tname = self.readStr(addr + self.payload(v, 0).offset);
                names = self.spliceNames(a, addr + self.payload(v, 1).offset, self.payload(v, 1).structName);
                k = 2;
            }
            vals: Vec<NodeId> = self.spliceList(a, addr + self.payload(v, k).offset, self.payload(v, k).structName);
            inits: Vec<InitNode>;
            for k in 0..vals.len() {
                nm: Sym = NO_SYM;
                if (k < names.len()) { nm = names.get(k); }
                inits.push(InitNode { name: nm, value: vals.get(k) });
            }
            first: long = a.addInits(inits);
            a.lits.push(LitNode { typeName: tname, firstInit: first, initCount: inits.len(), rest: NO_NODE });
            if (v == "TupleLit") { return a.leaf(Op.TupleLit, Payload.Lit(a.lits.len() - 1), Lit.Tuple); }
            return a.leafOf(Op.StructLit, Payload.Lit(a.lits.len() - 1), Lit.Struct, tname);
        }
        if (v == "VariantLit") {
            en: Sym = self.readStr(addr + self.payload(v, 0).offset);
            vn: Sym = self.readStr(addr + self.payload(v, 1).offset);
            args: Vec<NodeId> = self.spliceList(a, addr + self.payload(v, 2).offset, self.payload(v, 2).structName);
            return self.variantLit(a, en, vn, args);
        }
        if (v == "Splice") { failStr(stringOf("a macro returned a tree still holding a splice placeholder")); }
        failStr(format("a macro put a `{}` node where an expression belongs", v));
        return NO_NODE;
    }

    spliceList &self inout a:Ast addr:long sname:Sym -> Vec<NodeId> {
        out: Vec<NodeId>;
        buf: long = self.vecBuf(addr, sname);
        n: long = self.vecCount(addr, sname);
        w: long = typeBytes(Lit.Struct, self.nodeSym);
        for i in 0..n { out.push(self.spliceExpr(a, buf + i * w)); }
        return out;
    }
    spliceNames &self inout a:Ast addr:long sname:Sym -> Vec<Sym> {
        out: Vec<Sym>;
        buf: long = self.vecBuf(addr, sname);
        n: long = self.vecCount(addr, sname);
        for i in 0..n { out.push(self.readStr(buf + i * 16)); }
        return out;
    }

    // A statement Node as a statement; an expression Node becomes an expression statement.
    spliceStmt &self inout a:Ast addr:long -> long {
        v: str = self.nodeVariant(addr);
        if (v == "Block") {
            a.blockStmts.push(BlockStmtNode { body: self.spliceBlockStmt(a, addr) });
            return a.addStmt(StmtKind.Block, a.blockStmts.len() - 1);
        }
        if (v == "ExprStmt") {
            e: NodeId = self.spliceExpr(a, self.readBox(addr + self.payload(v, 0).offset));
            a.exprStmts.push(ExprStmtNode { value: e });
            return a.addStmt(StmtKind.Expr, a.exprStmts.len() - 1);
        }
        if (v == "Let") {
            init: NodeId = NO_NODE;
            ia: long = self.readBox(addr + self.payload(v, 2).offset);
            if (self.nodeVariant(ia) != "Nothing") { init = self.spliceExpr(a, ia); }
            t: TypeRef = unmangledType(nameOf(self.readStr(addr + self.payload(v, 1).offset)));
            n: Sym = self.declareHygienic(self.readStr(addr + self.payload(v, 0).offset));
            a.decls.push(VarDeclNode { name: n, kind: t.base, structName: t.name, isArray: false, count: 0,
                                       conv: Conv.None, isVariadic: false, elemKind: Lit.Void, elemStruct: NO_SYM,
                                       init: init });
            return a.addStmt(StmtKind.VarDecl, a.decls.len() - 1);
        }
        if (v == "If") { return a.addStmt(StmtKind.If, self.spliceIf(a, addr)); }
        if (v == "While") {
            c: NodeId = self.spliceExpr(a, self.readBox(addr + self.payload(v, 0).offset));
            b: long = self.spliceBlock(a, self.readBox(addr + self.payload(v, 1).offset));
            a.whiles.push(WhileNode { cond: c, body: b, step: -1 });
            return a.addStmt(StmtKind.While, a.whiles.len() - 1);
        }
        if (v == "Return") {
            va: long = self.readBox(addr + self.payload(v, 0).offset);
            val: NodeId = NO_NODE;
            if (self.nodeVariant(va) != "Nothing") { val = self.spliceExpr(a, va); }
            a.returns.push(ReturnNode { value: val });
            return a.addStmt(StmtKind.Return, a.returns.len() - 1);
        }
        if (v == "Break")    { return a.addStmt(StmtKind.Break, 0); }
        if (v == "Continue") { return a.addStmt(StmtKind.Continue, 0); }
        if (v == "Nothing") {
            ids: Vec<long>;
            a.blockStmts.push(BlockStmtNode { body: a.addBlock(ids) });
            return a.addStmt(StmtKind.Block, a.blockStmts.len() - 1);
        }
        e: NodeId = self.spliceExpr(a, addr);
        a.exprStmts.push(ExprStmtNode { value: e });
        return a.addStmt(StmtKind.Expr, a.exprStmts.len() - 1);
    }
    // A Block node (or any single statement) as a block id.
    spliceBlock &self inout a:Ast addr:long -> long {
        if (self.nodeVariant(addr) == "Block") { return self.spliceBlockStmt(a, addr); }
        ids: Vec<long>;
        ids.push(self.spliceStmt(a, addr));
        return a.addBlock(ids);
    }
    spliceBlockStmt &self inout a:Ast addr:long -> long {
        fd: FieldDef = self.payload("Block", 0);
        buf: long = self.vecBuf(addr + fd.offset, fd.structName);
        n: long = self.vecCount(addr + fd.offset, fd.structName);
        w: long = typeBytes(Lit.Struct, self.nodeSym);
        ids: Vec<long>;
        for i in 0..n { ids.push(self.spliceStmt(a, buf + i * w)); }
        return a.addBlock(ids);
    }
    // An If node as an IfNode index: the else is a Block (the parser's always-true last link),
    // another If, or Nothing.
    spliceIf &self inout a:Ast addr:long -> long {
        c: NodeId = self.spliceExpr(a, self.readBox(addr + self.payload("If", 0).offset));
        body: long = self.spliceBlock(a, self.readBox(addr + self.payload("If", 1).offset));
        ea: long = self.readBox(addr + self.payload("If", 2).offset);
        ev: str = self.nodeVariant(ea);
        chain: long = -1;
        if (ev == "If") { chain = self.spliceIf(a, ea); }
        else if (ev != "Nothing") {
            always: NodeId = a.leaf(Op.Literal, Payload.Num(1), Lit.Bool);
            a.ifs.push(IfNode { cond: always, body: self.spliceBlock(a, ea), elseIf: -1 });
            chain = a.ifs.len() - 1;
        }
        a.ifs.push(IfNode { cond: c, body: body, elseIf: chain });
        return a.ifs.len() - 1;
    }
}

// ─── derives: a type as a value, and declarations back as syntax ────────────
//
// A trait's derive macro (`trait Encode derive deriveEncode`) is handed the declaration of the
// type it writes an implementation for, as `stdlib::reflect`'s `Struct`, `Enum`, or a `Decl`
// holding either, built here from the registry's own tables. It returns a `MethodsDecl` Node,
// which is turned back into functions here for the checker to hold to the trait. The view's
// fields are filled by name, each only if the view declares it, so `reflect.k` may grow a field
// without this code knowing; that file documents what each field says.

methods Evaluator {
    // A `Variant(E, V, args)`: the struct literal the parser makes of `E.V(args)`, the tag and
    // then the variant's payload slots.
    variantLit &self inout a:Ast en:Sym vn:Sym args:Vec<NodeId> -> NodeId {
        ei: long = gReg.findEnumSym(en);
        if (ei < 0) {
            q: Sym = gReg.resolveBare(stemOf(nameOf(self.macroFile)), nameOf(en));
            ei = gReg.findEnumSym(q);
            if (ei >= 0) { en = q; }
        }
        if (ei < 0) { failStr(format("a macro built a variant of `{}`, which is not a sum type", nameOf(en))); }
        d: EnumDef = gReg.enumDef(ei);
        vi: long = gReg.findVariant(d, nameOf(vn));
        if (vi < 0) { failStr(format("no variant `{}` in enum `{}`\nnote: a macro built `{}.{}`", nameOf(vn), nameOf(en), nameOf(en), nameOf(vn))); }
        vd: VariantDef = gReg.variantAt(d, vi);
        if (vd.payloadCount != args.len()) {
            failStr(format("a macro built `{}.{}` with the wrong number of values: expected {}, found {}", nameOf(en), nameOf(vn), vd.payloadCount, args.len()));
        }
        inits: Vec<InitNode>;
        inits.push(InitNode { name: intern(enumTagField()), value: a.leaf(Op.Literal, Payload.Num(vd.value), d.backing) });
        for k in 0..args.len() {
            inits.push(InitNode { name: enumPayloadField(nameOf(vn), k), value: args.get(k) });
        }
        first: long = a.addInits(inits);
        a.lits.push(LitNode { typeName: en, firstInit: first, initCount: inits.len(), rest: NO_NODE });
        return a.leafOf(Op.StructLit, Payload.Lit(a.lits.len() - 1), Lit.Struct, en);
    }

    // ─── the view ────────────────────────────────────────────────────────────

    // The declaration of `owner` as a value of the view type `view` (a struct the derive macro's
    // parameter names), built on the compile-time stack. Returns its address.
    reflectView &self owner:Sym view:Sym -> long {
        at: long = self.alloc(typeBytes(Lit.Struct, view));
        v: str = lastComponentOf(nameOf(view));
        isEnum: bool = gReg.findEnumSym(owner) >= 0;
        if (v == "Struct") { self.putStructView(at, view, owner); return at; }
        if (v == "Enum") { self.putEnumView(at, view, owner); return at; }
        // `Decl`: whichever of the two it is, as that variant.
        ed: EnumDef = gReg.enumDef(gReg.findEnumSym(view));
        arm: str = "OfStruct";
        if (isEnum) { arm = "OfEnum"; }
        vi: long = gReg.findVariant(ed, arm);
        if (vi < 0) { failStr(format("no variant `{}` in enum `{}`\nnote: the compiler needs it to describe a type to a derive macro", arm, nameOf(view))); }
        self.store(at + self.viewField(view, enumTagField()).offset, ed.backing, NO_SYM, gReg.variantAt(ed, vi).value);
        slot: FieldDef = self.viewField(view, nameOf(enumPayloadField(arm, 0)));
        if (isEnum) { self.putEnumView(at + slot.offset, slot.structName, owner); }
        else { self.putStructView(at + slot.offset, slot.structName, owner); }
        return at;
    }
    putStructView &self at:long view:Sym owner:Sym -> void {
        d: StructDef = gReg.structDef(gReg.findStructSym(owner));
        self.putViewStr(at, view, "name", nameOf(owner));
        fs: FieldDef = self.viewField(view, "fields");
        elem: Sym = ctVecElem(fs.structName);
        w: long = typeBytes(Lit.Struct, elem);
        buf: long = 0;
        if (d.fieldCount > 0) { buf = self.ctMalloc(d.fieldCount * w); }
        for k in 0..d.fieldCount {
            f: FieldDef = gReg.fieldAt(d, k);
            self.putFieldView(buf + k * w, elem, f);
        }
        self.putVec(at + fs.offset, fs.structName, buf, d.fieldCount);
    }
    putEnumView &self at:long view:Sym owner:Sym -> void {
        ed: EnumDef = gReg.enumDef(gReg.findEnumSym(owner));
        // An enum of named integers has no struct row: it is just its backing integer, with no tag.
        si: long = gReg.findStructSym(owner);
        self.putViewStr(at, view, "name", nameOf(owner));
        self.putViewLong(at, view, "isBacked", Lit.Bool, ctBit(!ed.hasPayload));
        self.putViewStr(at, view, "backing", typeName(ed.backing));
        if (ed.hasPayload) { self.putViewStr(at, view, "tagField", enumTagField()); }
        vs: FieldDef = self.viewField(view, "variants");
        velem: Sym = ctVecElem(vs.structName);
        vw: long = typeBytes(Lit.Struct, velem);
        vbuf: long = 0;
        if (ed.variantCount > 0) { vbuf = self.ctMalloc(ed.variantCount * vw); }
        ps: FieldDef = self.viewField(velem, "payloads");
        pelem: Sym = ctVecElem(ps.structName);
        pw: long = typeBytes(Lit.Struct, pelem);
        for k in 0..ed.variantCount {
            vd: VariantDef = gReg.variantAt(ed, k);
            va: long = vbuf + k * vw;
            self.putViewStr(va, velem, "name", nameOf(vd.name));
            self.putViewLong(va, velem, "tag", Lit.Long, vd.value);
            pbuf: long = 0;
            if (vd.payloadCount > 0) { pbuf = self.ctMalloc(vd.payloadCount * pw); }
            for j in 0..vd.payloadCount {
                if (si >= 0) {
                    sd: StructDef = gReg.structDef(si);
                    fi: long = gReg.findField(sd, nameOf(enumPayloadField(nameOf(vd.name), j)));
                    if (fi >= 0) { self.putFieldView(pbuf + j * pw, pelem, gReg.fieldAt(sd, fi)); }
                }
            }
            self.putVec(va + ps.offset, ps.structName, pbuf, vd.payloadCount);
        }
        self.putVec(at + vs.offset, vs.structName, vbuf, ed.variantCount);
    }
    // One field (or one variant's payload slot) as a `Field`.
    putFieldView &self at:long view:Sym f:FieldDef -> void {
        self.putViewStr(at, view, "name", nameOf(f.name));
        self.putViewStr(at, view, "typeName", typeMangleName(f.kind, f.structName));
        self.putViewLong(at, view, "isRawPointer", Lit.Bool, ctBit(f.kind == Lit.Ptr));
        self.putViewLong(at, view, "isFn", Lit.Bool, ctBit(f.kind == Lit.Fn));
        self.putViewLong(at, view, "isTraitObject", Lit.Bool, ctBit(f.kind == Lit.TraitObj));
        self.putViewLong(at, view, "isArray", Lit.Bool, ctBit(f.isArray));
        self.putViewLong(at, view, "count", Lit.Long, f.count);
    }
    putViewStr &self at:long view:Sym field:str text:str -> void {
        fi: long = self.viewFieldAt(view, field);
        if (fi < 0) { return; }
        self.putStr(at + gReg.fieldAt(gReg.structDef(gReg.findStructSym(view)), fi).offset, text);
    }
    putViewLong &self at:long view:Sym field:str k:Lit v:long -> void {
        fi: long = self.viewFieldAt(view, field);
        if (fi < 0) { return; }
        self.store(at + gReg.fieldAt(gReg.structDef(gReg.findStructSym(view)), fi).offset, k, NO_SYM, v);
    }
    viewFieldAt &self view:Sym field:str -> long {
        si: long = gReg.findStructSym(view);
        if (si < 0) { return -1; }
        return gReg.findField(gReg.structDef(si), field);
    }
    // A field the view cannot do without.
    viewField &self view:Sym field:str -> FieldDef {
        fi: long = self.viewFieldAt(view, field);
        if (fi < 0) { failStr(format("no field `{}` on type `{}`\nnote: the compiler needs it to describe a type to a derive macro", field, nameOf(view))); }
        return gReg.fieldAt(gReg.structDef(gReg.findStructSym(view)), fi);
    }

    // ─── declarations ────────────────────────────────────────────────────────

    // A `MethodsDecl`'s header, as spelled: the type, and the trait ("" for none).
    declOwner &self addr:long -> Sym { return self.readStr(addr + self.payload("MethodsDecl", 0).offset); }
    declTrait &self addr:long -> Sym { return self.readStr(addr + self.payload("MethodsDecl", 1).offset); }
    // Its `FnDecl`s, by address, in the order written.
    declFns &self addr:long -> Vec<long> {
        fd: FieldDef = self.payload("MethodsDecl", 2);
        buf: long = self.vecBuf(addr + fd.offset, fd.structName);
        n: long = self.vecCount(addr + fd.offset, fd.structName);
        w: long = typeBytes(Lit.Struct, self.nodeSym);
        out: Vec<long>;
        for i in 0..n { out.push(buf + i * w); }
        return out;
    }
    fnDeclName &self addr:long -> Sym {
        if (self.nodeVariant(addr) != "FnDecl") { failStr(format("a `methods` block holds a `{}` node where a method (`FnDecl`) belongs", self.nodeVariant(addr))); }
        return self.readStr(addr + self.payload("FnDecl", 0).offset);
    }
    // Turns one `FnDecl` into the function `name`, a method of `owner`. Its parameters are
    // declared, and its body is spliced with the hygiene every macro's statements get, as if
    // written in `file`/`pkg` (where its bare names resolve). It is not added to the tree's
    // function list; the caller puts it in place.
    spliceFnDecl &self inout a:Ast addr:long owner:Sym name:Sym file:Sym pkg:Sym -> FnNode {
        pd: FieldDef = self.payload("FnDecl", 1);
        buf: long = self.vecBuf(addr + pd.offset, pd.structName);
        n: long = self.vecCount(addr + pd.offset, pd.structName);
        w: long = typeBytes(Lit.Struct, self.nodeSym);
        params: Vec<long>;
        for k in 0..n {
            p: long = buf + k * w;
            if (self.nodeVariant(p) != "ParamDecl") { failStr(format("the parameter list of `{}` holds a `{}` node where a parameter (`ParamDecl`) belongs", nameOf(name), self.nodeVariant(p))); }
            pn: Sym = self.readStr(p + self.payload("ParamDecl", 0).offset);
            t: TypeRef = self.spelledType(nameOf(self.readStr(p + self.payload("ParamDecl", 1).offset)), owner);
            cs: str = nameOf(self.readStr(p + self.payload("ParamDecl", 2).offset));
            conv: Conv = Conv.None;
            if (cs == "inout") { conv = Conv.Inout; if (t.base == Lit.Struct) { t = TypeRef { base: Lit.Ref, name: t.name }; } }
            else if (cs == "sink") { conv = Conv.Sink; }
            else if (cs == "read") { conv = Conv.Read; }
            else if (cs.len > 0) { failStr(format("unknown parameter convention `{}` in `{}`\nnote: a parameter is taken `inout`, `sink` or `read`, or written with no convention", cs, nameOf(name))); }
            // The receiver says how it is taken by its type, as `&self` and `self` do in source.
            if (k == 0 && nameOf(pn) == "self" && cs.len == 0) {
                if (t.base == Lit.Ref) { conv = Conv.Inout; } else { conv = Conv.Sink; }
            }
            a.decls.push(VarDeclNode { name: pn, kind: t.base, structName: t.name, isArray: false, count: 0,
                                       conv: conv, isVariadic: false, elemKind: Lit.Void, elemStruct: NO_SYM,
                                       init: NO_NODE });
            params.push(a.decls.len() - 1);
        }
        ret: TypeRef = self.spelledType(nameOf(self.readStr(addr + self.payload("FnDecl", 2).offset)), owner);
        body: long = self.spliceBlock(a, self.readBox(addr + self.payload("FnDecl", 3).offset));
        firstArg: long = a.addParams(params);
        return FnNode { name: name, returnKind: ret.base, returnStruct: ret.name, visibility: Vis.Pub,
                        file: file, pkg: pkg, isUnsafe: false, isTemplate: false, inferReturn: false,
                        firstBound: 0, boundCount: 0, firstArg: firstArg, argCount: params.len(), body: body };
    }
    // A type as a declaration Node spells it. `Self` and `ref_Self` are the type the methods are
    // for; a trait's name is a trait object, as it is where a type is written.
    spelledType &self s:str owner:Sym -> TypeRef {
        if (s == "Self" || s == "ref_Self") {
            if (namesScalar(nameOf(owner))) { return TypeRef { base: scalarNamed(nameOf(owner)), name: NO_SYM }; }
            if (s == "Self") { return TypeRef { base: Lit.Struct, name: owner }; }
            return TypeRef { base: Lit.Ref, name: owner };
        }
        if (s.len == 0) { return TypeRef { base: Lit.Void, name: NO_SYM }; }
        t: TypeRef = unmangledType(s);
        if (t.base == Lit.Struct && gReg.findTraitSym(t.name) >= 0) { return TypeRef { base: Lit.TraitObj, name: t.name }; }
        return t;
    }
}

local ctBit b:bool -> long { if (b) { return 1; } return 0; }

// The element type of a `Vec<T>` instance, from the request that stamped it.
local ctVecElem inst:Sym -> Sym {
    r: long = gReg.findRequestSym(inst);
    if (r < 0) { failStr(format("`{}` is not a `Vec` instance the compiler stamped", nameOf(inst))); }
    return gReg.gArgAt(gReg.requestAt(r), 0).name;
}

// ─── a dependency's globals ──────────────────────────────────────────────────
//
// A package build does not run its dependencies' initializers: each was folded where its package
// was compiled, and the result travels in that package's facts as the bytes promotion wrote, with
// every pointer word named (a string literal, a heap block, a global, a vtable, a function). Read
// here, those names are turned back into this evaluator's own addresses, so compile-time code
// reads the value exactly as if the initializer had run in this compile. A global its package
// initializes at startup has no value here, and reading one is refused, as reading any global an
// earlier startup initializer may write is.

methods Evaluator {
    loadExternGlobal &self inout a:Ast n:Sym addr:long -> void {
        self.extReady.put(nameOf(n), true);
        gi: long = gFacts.globalFact(n);
        if (gi < 0) { self.stop(format("the global `{}`, which its package's `.klib` records nothing about", nameOf(n))); return; }
        g: GlobalFact = gFacts.globals.get(gi);
        if (g.state == GlobalState.Startup) {
            self.stop(format("the global `{}`, which its package initializes at startup", nameOf(n)));
            return;
        }
        if (g.state == GlobalState.Zero) { return; }      // storage starts zeroed, as it does here
        if (g.state == GlobalState.Scalar) {
            di: long = gReg.findGlobalSym(n);
            if (di < 0) { self.stop(format("the global `{}`, which nothing declares", nameOf(n))); return; }
            gd: GlobalDef = gReg.globalDef(di);
            k: Lit = storedKind(gd.kind, gd.structName);
            w: long = typeInfo(k).size;
            if (w < 1 || w > 8) { w = 8; }
            self.putBits(addr, w, g.value);
            return;
        }
        self.loadImage(a, g.image, addr);
    }

    // Image `img` of the facts, its bytes at `addr` and its pointer words aimed at this run's
    // copies of what they name.
    loadImage &self inout a:Ast img:long addr:long -> void {
        im: ImgFact = gFacts.images.get(img);
        for k in 0..im.byteCount { self.rawSet(addr + k, gFacts.bytes.get(im.firstByte + k)); }
        k: long = 0;
        while (k < im.relocCount && !self.stopped) {
            r: RelocFact = gFacts.relocs.get(im.firstReloc + k);
            k = k + 1;
            v: long = 0;
            if (r.kind == RelocKind.Str) {
                v = self.literalStart(r.target) + r.delta;
            } else if (r.kind == RelocKind.Block) {
                v = self.externBlock(a, r.image) + r.delta;
            } else if (r.kind == RelocKind.Global) {
                hit: Option<long> = self.globalAddr.find(nameOf(r.target));
                ga: long = -1;
                match hit { Some(p) { ga = p; } None { } }
                if (ga < 0) { self.stop(format("a pointer to the global `{}`, which this program does not hold", nameOf(r.target))); return; }
                if (isExternGlobal(r.target) && !self.extReady.has(nameOf(r.target))) { self.loadExternGlobal(a, r.target, ga); }
                v = ga + r.delta;
            } else if (r.kind == RelocKind.Fn) {
                fh: Option<long> = self.fnAt.find(r.target as long);
                fi: long = -1;
                match fh { Some(i) { fi = i; } None { } }
                if (fi < 0) { self.stop(format("a pointer to `{}`, a function this package has not stamped", nameOf(r.target))); return; }
                v = FN_BASE + fi;
            } else {
                v = self.vtableHandle(r.concrete, r.trait);
            }
            self.putBits(addr + r.offset, 8, v);
        }
    }

    // A heap block of a dependency's image, allocated and filled once however many pointers
    // reach it, so shared structure stays shared.
    externBlock &self inout a:Ast img:long -> long {
        while (self.extBlocks.len() < gFacts.images.len()) { self.extBlocks.push(-1); }
        at: long = self.extBlocks.get(img);
        if (at >= 0) { return at; }
        im: ImgFact = gFacts.images.get(img);
        at = self.ctMalloc(im.byteCount);
        self.extBlocks.set(img, at);
        self.loadImage(a, img, at);
        return at;
    }

    // Writes a word where nothing else may write, bypassing `writable`: loading from the facts
    // is the same kind of commit `foldInit` makes.
    putBits &self addr:long w:long v:long -> void {
        x: long = v;
        for i in 0..w { self.rawSet(addr + i, (x & 255) as u8); x = x >> 8; }
    }
}

// Whether the place `id` names is `n` or a part of it: `n`, a field or element of it, `&` of one.
local rootedAt inout a:Ast id:NodeId n:Sym -> bool {
    cur: NodeId = id;
    while (cur != NO_NODE) {
        e: Expr = a.expr(cur);
        match e.payload {
            Name(x) { return e.op == Op.Lvalue && x == n; }
            Sub(v) { cur = v; }
            Field(f) { cur = a.fields.get(f).base; }
            Index(i) {
                ix: IndexNode = a.indexes.get(i);
                if (ix.base == NO_NODE) { return ix.name == n; }
                cur = ix.base;
            }
            _ { return false; }
        }
    }
    return false;
}
