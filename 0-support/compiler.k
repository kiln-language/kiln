// The three things every phase shares: interned names, the source text those names point into,
// and how a problem is reported.
//
// Three globals and the policy for stopping. Everything that was general here moved into the
// standard library, where the rest of the language can have it.
#include <stdlib::{cmp, encode, heap, intern, mem, io, option, result, string, sys, textfile, time, vec}>

// A name, as an index into `gNames`. Comparing two is an integer compare, and a `Sym` is `Copy`,
// so it can be a map key, an enum payload or a struct field without owning anything.
//
// A type of its own rather than an alias of `long`: a backed enum with no variants is stored and
// passed as the integer it is, so this costs nothing, and it gives `Encode`/`Decode` a type to
// answer for. An index means nothing in another process, so a name crosses into a `.klib` as its
// spelling, through the string table below; every record that holds one derives its codec and
// gets that for free.
pub enum Sym: long { }
pub NO_SYM: Sym = -1;

// Ordered and hashed as the number it is: a sorted list of names (the import closure) is
// sorted by interning order, which is all a binary search over it needs.
methods Sym for Ord {
    cmp &self other:Sym -> int {
        a: long = self as long;
        b: long = other as long;
        if (a < b) { return -1; }
        if (a > b) { return 1; }
        return 0;
    }
}
methods Sym for Hash { hash &self -> u64 { return mixHash((self as long) as u64); } }

// One interner for the whole compile. The C++ front end kept its registries in thread-local
// globals for the same reason: every phase turns names into symbols, and threading an interner
// through every signature buys nothing when there is exactly one.
pub var gNames: Interner;

pub intern s:str -> Sym  { return gNames.intern(s); }
pub nameOf id:Sym -> str { return gNames.nameOf(id); }

// Intern `s` and hand back the interner's own copy: a `str` that outlives whatever buffer the
// text came from.
pub keep s:str -> str { return gNames.keep(s); }

// The same two for text that was just built. Interning copies, so neither needs the caller to
// take an `unsafe` view of the String it assembled, which is most of what `unsafe` was marking
// in this compiler.
pub internString s:String -> Sym { return gNames.internString(s); }
pub keepString   s:String -> str { return gNames.keepString(s); }

// ─── names in a `.klib` ──────────────────────────────────────────────────────
// A package's metadata holds every name it mentions once, in a string table, and a name anywhere
// else in it is a position in that table plus one (0 is no name). Writing, the table is filled
// in order of first use, so the same compile writes the same bytes. Reading, a position becomes
// a name the first time something decodes it, and every later decode of it is a vector read:
// a name the dependent never looks at is never interned.

// Writing: per name, its position in the table, or -1; and the table, in order.
pub var gSymOut: Vec<long> = vec![];
pub var gSymTable: Vec<Sym> = vec![];
// Reading: every loaded package's table, one after another. Per entry its spelling (a view into
// the metadata, which is kept) and the name it was interned as, `SYM_UNREAD` until then. A
// package's names are `gSymInBase` onward, `gSymInCount` of them: set while one is decoded.
pub var gSymInText: Vec<str> = vec![];
pub var gSymIn: Vec<Sym> = vec![];
pub var gSymInBase: long = 0;
pub var gSymInCount: long = 0;
pub SYM_UNREAD: Sym = -2;

// The table position a name is written as, entering it the first time.
pub symOut s:Sym -> long {
    n: long = s as long;
    if (n < 0) { return -1; }
    while (gSymOut.len() <= n) { gSymOut.push(-1); }
    at: long = gSymOut.get(n);
    if (at < 0) {
        at = gSymTable.len();
        gSymOut.set(n, at);
        gSymTable.push(s);
    }
    return at;
}
// Start a new table (a compile writes one package's).
pub symOutReset -> void {
    for s in gSymTable { gSymOut.set(s as long, -1); }
    gSymTable.clear();
}

methods Sym for Encode {
    encode &self out:&Encoder -> void { out.putUvarint((symOut(self) + 1) as u64); }
}
methods Sym for Decode {
    decode inp:&Decoder -> Sym { return symAt(inp, inp.getUvarint() as long); }
}

// The name written as `t` (its place in the table plus one; 0 is none), in the table being read.
pub symAt inp:&Decoder t:long -> Sym {
    if (t == 0) { return NO_SYM; }
    if (t < 0 || t > gSymInCount) { inp.fail("a name past the end of the string table"); return NO_SYM; }
    at: long = gSymInBase + t - 1;
    s: Sym = gSymIn.get(at);
    if (s == SYM_UNREAD) {
        s = intern(gSymInText.get(at));
        gSymIn.set(at, s);
    }
    return s;
}

// `stdlib` is a package like any other and is named like one: `<stdlib::io>`, the way Rust writes
// `std::`. It is the one package nobody has to declare a dependency on, because a standalone
// program has no manifest to declare it in: implicitly available, explicitly named. Here, where
// every phase can reach it: the preprocessor resolves includes against it, the scanner pulls
// `core` and `ast` from it, and an error names a module of it to include.
pub STDLIB_PKG:  str = "stdlib";
pub STDLIB_ROOT: str = "stdlib";

// ─── source text ─────────────────────────────────────────────────────────────
// Every `str` the compiler holds (a token's spelling, a diagnostic's quoted line) points into
// one of these, so they are kept for the life of the process. That is the same bargain the C++
// front end made with its Arena: a compiler runs once and exits, so releasing is work with no
// observer.
local var gSources: Vec<String>;

// The text of `path`, or `None` if it cannot be opened. The caller decides whether a miss is an
// error: the package map walks up past directories with no manifest, and only the driver treats
// a missing file as fatal.
pub tryReadSource path:str -> Option<str> {
    r: Result<String, long> = readFileString(path);
    match r {
        Err(_) { return Option.None; }
        Ok(text) {
            view: str = "";
            unsafe { view = text.view(); }   // held below, so these bytes outlive this call
            gSources.push(text);
            return Option.Some(view);
        }
    }
}

// Text that was not read from a file of its own (a member of an archive) kept the same way, for
// the life of the process, with a view handed back.
pub holdSource text:String -> str {
    view: str = "";
    unsafe { view = text.view(); }
    gSources.push(text);
    return view;
}

pub readSource path:str -> str {
    hit: Option<str> = tryReadSource(path);
    match hit { Some(t) { return t; } None { } }
    failStr(format("could not open '{}'", path));
    return "";
}

// ─── where the time goes ─────────────────────────────────────────────────────
// `--time-phases`. Guessing at this has been wrong three times: the assembler turned out to be a
// third of a build, name resolution turned out to be quadratic, and the ownership pass turned out
// to be the largest phase in the compiler while being invisible from outside as a phase at all.
// So the compiler reports its own, and every phase can reach the clock.
pub var gTimePhases: bool = false;
pub var gPhaseAt: Instant = Instant { secs: 0, nanos: 0 };

pub phaseStart -> void { if (gTimePhases) { gPhaseAt = monotonic(); } }
pub phaseEnd name:str -> void {
    if (!gTimePhases) { return; }
    eprintln("  {}: {} ms", name, elapsedUs(gPhaseAt) / 1000);
    gPhaseAt = monotonic();
}

// ─── diagnostics ─────────────────────────────────────────────────────────────
// There are no exceptions, so an error is not thrown and caught: it is written to stderr and the
// process exits. That is what the C++ front end did anyway once the top-level handler printed
// the message: the catch only ever added a frame.
pub COMPILE_FAILED: long = 1;

// ─── where in the source ─────────────────────────────────────────────────────
// A position is one word: `(file << 40) | (line << 16) | column`, the file an index into
// `gPosFiles` from 1, and 0 for no position at all. Every statement has one (`Ast.stmtPos`, a
// column beside the statements rather than a field on every node), and `gPos` is the one the
// compiler is working on now: the parser sets it as it reads each statement, and every later pass
// as it walks one. A statement a pass writes itself is stamped with it, so it reports where the
// code it was written for stands. An error with no source to blame (a missing file, an archive)
// is reported where `gPos` is 0, which the driver makes it between phases.
pub var gPos: long = 0;
pub var gPosFiles: Vec<Sym> = vec![];
local var gPosLastFile: long = -1;      // the file the last lookup asked for, as a Sym's number
local var gPosLastIdx: long = 0;

pub posFileIndex f:Sym -> long {
    if (f == NO_SYM) { return 0; }
    if (f as long == gPosLastFile) { return gPosLastIdx; }
    k: long = 0;
    while (k < gPosFiles.len() && gPosFiles.get(k) != f) { k = k + 1; }
    if (k == gPosFiles.len()) { gPosFiles.push(f); }
    gPosLastFile = f as long;
    gPosLastIdx = k + 1;
    return k + 1;
}
pub posOf f:Sym line:long col:long -> long {
    fi: long = posFileIndex(f);
    if (fi == 0) { return 0; }
    l: long = line;
    if (l < 0) { l = 0; }
    if (l > 16777215) { l = 16777215; }
    c: long = col;
    if (c < 0) { c = 0; }
    if (c > 65535) { c = 65535; }
    return (fi << 40) | (l << 16) | c;
}
pub posFile p:long -> Sym {
    i: long = p >> 40;
    if (i <= 0 || i > gPosFiles.len()) { return NO_SYM; }
    return gPosFiles.get(i - 1);
}
pub posLine p:long -> long { return (p >> 16) & 16777215; }
pub posCol p:long -> long { return p & 65535; }

// ─── what a diagnostic says besides its message ──────────────────────────────
// An error inside a generic instance or a derive also says where that instance was asked for,
// back to the user's code; the compiler's own (`internal: ...`) says what it was doing. And a type
// is named as it is written (`Option<long>`, not `option::Option_long`). The tables that know all
// that are the registry's, above this module, so they reach the error path through two hooks
// `parse::diag` installs (`installDiagnostics`); until then a message is printed as it is.
pub var gPhase: str = "";          // what the driver is running: "type-checking", "lowering", ...
pub var gCtxFn: Sym = NO_SYM;      // the function the phase is working on, for the notes
local spellAsIs msg:str -> String { return stringOf(msg); }
local noNotes msg:str -> void { }
pub var gSpellHook: fn(str) -> String = &spellAsIs;
pub var gNoteHook: fn(str) -> void = &noNotes;
local var gInFail: bool = false;   // a hook that fails is not given a second chance

// ─── going on past an error ──────────────────────────────────────────────────
// A phase that works function by function arms a recovery point around each one
// (`armRecovery`): an error inside is reported, and the phase goes on with the next function
// instead of stopping, up to `MAX_ERRORS`. At the end of that phase the compile stops if there was
// any (`stopIfErrors`), so no later phase sees a function an error cut short. Work an error would
// leave half done in a way the next function could trip over (a macro running in the evaluator,
// an implementation being stamped) holds `gNoResume`, and an error there stops at once, as one
// with no recovery point armed does.
pub var gErrorCount: long = 0;
pub MAX_ERRORS: long = 20;
pub var gNoResume: long = 0;
local var gResumeArmed: bool = false;
local var gJmp: [long; 8];         // the caller's rbp, resume address, rsp, then r12..r15

// A recovery point, in the manner of `setjmp`: answers 0 when armed, and 1 a second time, later,
// when an error under it was reported and the caller should abandon what it was doing. Saved from
// this function's own frame (the prologue is `push rbp; mov rbp, rsp`): the caller's rbp, the
// address the call returns to, the caller's rsp once it has, and r12-r15, the registers this
// compiler's convention has a callee preserve; every other register a call clobbers anyway, so
// the caller holds nothing there. Nothing in this body uses a callee-saved register, so those
// four are still the caller's. Never inlined: a function holding `asm` is not. The caller must
// arm immediately before the work it protects and change nothing it reads after a resume in
// between, since a register holding such a value comes back as it was when armed.
pub unsafe armRecovery -> long {
    buf: long = &gJmp as long;
    asm {
        in rcx buf;
        "mov rax, [rbp]"
        "mov [rcx], rax"
        "mov rax, [rbp + 8]"
        "mov [rcx + 8], rax"
        "lea rax, [rbp + 16]"
        "mov [rcx + 16], rax"
        "mov [rcx + 24], r12"
        "mov [rcx + 32], r13"
        "mov [rcx + 40], r14"
        "mov [rcx + 48], r15"
    }
    gResumeArmed = true;
    return 0;
}
pub disarmRecovery -> void { gResumeArmed = false; }
// Whether a phase may arm one now: not inside another, and not past the cap.
pub canRecover -> bool { return !gResumeArmed && gErrorCount < MAX_ERRORS - 1; }

// Back to the armed point, as `armRecovery` answering 1 (`longjmp`).
local unsafe resumeRecovery -> void {
    gResumeArmed = false;
    buf: long = &gJmp as long;
    asm {
        in rcx buf;
        "mov r12, [rcx + 24]"
        "mov r13, [rcx + 32]"
        "mov r14, [rcx + 40]"
        "mov r15, [rcx + 48]"
        "mov rbp, [rcx]"
        "mov rsp, [rcx + 16]"
        "mov eax, 1"
        "jmp qword [rcx + 8]"
    }
}

// The end of a phase that went on past its errors: stop if there were any.
pub stopIfErrors -> void {
    if (gErrorCount == 0) { return; }
    if (gErrorCount > 1) { eprintln("{} errors", gErrorCount); }
    flushErr();
    sysExit(COMPILE_FAILED);
}

// Every error past the parser says where, as the parser's own do: `file:line:col: Error: ...`,
// then its notes (`note: ...`, one per line).
pub fail msg:str -> never {
    nested: bool = gInFail;
    gInFail = true;
    // A call through a function value is taken to write what it is handed (the guard cannot see
    // its callee), and `fail` is handed immutable globals (`fail(USAGE)`): the hooks get a copy.
    m: str = msg;
    text: String;
    if (nested) { text = stringOf(msg); } else { text = gSpellHook(m); }
    if (gPos != 0) {
        f: Sym = posFile(gPos);
        where: str = "<input>";
        if (f != NO_SYM) { where = nameOf(f); }
        eprint("{}:{}:{}: ", where, posLine(gPos), posCol(gPos));
        eprintln("Error: {}", text);
    } else {
        eprintln("Error: {}", text);
    }
    if (!nested) { gNoteHook(m); }
    flushErr();
    gErrorCount = gErrorCount + 1;
    if (!nested && gResumeArmed && gNoResume == 0 && gErrorCount < MAX_ERRORS) {
        gInFail = false;
        unsafe { resumeRecovery(); }
    }
    if (gErrorCount > 1) {
        if (gErrorCount >= MAX_ERRORS) { eprintln("{} errors; stopping", gErrorCount); }
        else { eprintln("{} errors", gErrorCount); }
    }
    flushErr();
    sysExit(COMPILE_FAILED);
}

// `file:line:col: message`, the form every editor can jump to. A missing file prints `<input>`.
//
// No `Error: ` banner. The reference does not put one in front of the location: its parser emits
// `file:line:col: Expected a statement, but found …` with no banner at all, and its lexer's
// callers write one into the message they hand over, so it lands after the location. Prefixing
// here inverted every positioned diagnostic in the port: all eight of the lexer's, and the
// parser's, which should have none. A caller that wants a banner puts it in `msg`.
pub failAt file:str line:long col:long msg:str -> never {
    where: str = file;
    if (file.len == 0) { where = "<input>"; }
    nested: bool = gInFail;
    gInFail = true;
    m: str = msg;                      // a copy for the hook, as in `fail`
    text: String;
    if (nested) { text = stringOf(msg); } else { text = gSpellHook(m); }
    eprintln("{}:{}:{}: {}", where, line, col, text);
    if (gErrorCount > 0) { eprintln("{} errors", gErrorCount + 1); }
    flushErr();
    sysExit(COMPILE_FAILED);
}

// `fail` for a message that had to be assembled: almost always by `format`. Takes the String
// rather than a view of it so the call site is one line and cannot outlive its own buffer.
pub failStr s:String -> never { unsafe { fail(s.view()); } }

pub failAtStr file:str line:long col:long s:String -> never {
    unsafe { failAt(file, line, col, s.view()); }
}
