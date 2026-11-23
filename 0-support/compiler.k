// What every phase of the compiler shares: interned names (and how a name is written into a
// `.klib`), the source text those names point into, where in that text the compiler is working,
// and how a problem is reported and when the compile stops.
#include <stdlib::{cmp, encode, heap, intern, mem, io, option, recover, result, string, sys, textfile, time, vec}>

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

// One interner for the whole compile. Every phase turns names into symbols, and threading an
// interner through every signature buys nothing when there is exactly one.
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

// A name the compiler makes, `<pre><n><tail>` (`.GD12`, `.IL7_.L0`), interned without `format`:
// the inliner makes one per site and per label, and boxing the arguments cost more than the name.
pub madeName pre:str n:long tail:str -> Sym {
    s: String;
    s.pushStr(pre);
    s.pushLong(n);
    s.pushStr(tail);
    return internString(s);
}

// The Sym `s` already is, or NO_SYM, without interning it. A table keyed by names' numbers is
// asked this way when the caller holds only text: a name that was never interned cannot be in it.
pub symIfAny s:str -> Sym {
    hit: Option<long> = gNames.lookup(s);
    match hit { Some(id) { return id as Sym; } None { } }
    return NO_SYM;
}

// ─── names in a `.klib` ──────────────────────────────────────────────────────
// A package's metadata holds every name it mentions once, in a string table, and a name anywhere
// else in it is a position in that table plus one (0 is no name). When writing, the table is
// filled in order of first use, so the same compile writes the same bytes. When reading, a
// position becomes a name the first time something decodes it, and every later decode of it is a
// vector read, so a name the dependent never looks at is never interned.

// Writing: per name, its position in the table, or -1; and the table, in order.
pub var gSymOut: Vec<long> = vec![];
pub var gSymTable: Vec<Sym> = vec![];
// Reading: every loaded package's table, one after another. Each entry has its spelling (a view
// into the metadata, which is kept) and the name it was interned as, `SYM_UNREAD` until it is.
// While a package is being decoded, its names are the `gSymInCount` entries from `gSymInBase`.
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
// program has no manifest to declare it in: implicitly available, explicitly named. It is defined
// here because every phase needs it: the preprocessor resolves includes against it, the scanner
// pulls `core` and `ast` from it, and an error can name one of its modules to include.
pub STDLIB_PKG:  str = "stdlib";
pub STDLIB_ROOT: str = "stdlib";

// ─── source text ─────────────────────────────────────────────────────────────
// Every `str` the compiler holds (a token's spelling, a diagnostic's quoted line) points into
// one of these, so they are kept for the life of the process. A compiler runs once and exits,
// so freeing them would be work that nobody could observe.
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
    failStr(format("cannot open `{}`", path));
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
// There are no exceptions, so an error is not thrown and caught. It is written to stderr, and
// then either the phase picks up again at the recovery point it armed (below) or the process
// exits with `COMPILE_FAILED`.
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
// back to the user's code, and an internal compiler error says what the compiler was doing. A
// type is named as it is written (`Option<long>`, not `option::Option_long`). The tables that
// know all that belong to the registry, which sits above this module, so they reach the error
// path through two hooks that `parse::diag` installs (`installDiagnostics`). Until then a
// message is printed as it is.
pub var gPhase: str = "";          // what the driver is running: "type-checking", "lowering", ...
pub var gCtxFn: Sym = NO_SYM;      // the function the phase is working on, for the notes
local spellAsIs msg:str -> String { return stringOf(msg); }
local noNotes msg:str -> void { }
pub var gSpellHook: fn(str) -> String = &spellAsIs;
pub var gNoteHook: fn(str) -> void = &noNotes;
local var gInFail: bool = false;   // a hook that fails is not given a second chance

// ─── going on past an error ──────────────────────────────────────────────────
// A phase that works function by function runs each one in the body of a `recover`, and the
// parser each top-level declaration: an error inside is reported, `fail` or `failAt` raises, and
// the phase goes on with the next one instead of stopping, up to `MAX_ERRORS`. At the end of that
// phase the compile stops if there was any (`stopIfErrors`), so no later phase sees a function or
// a declaration an error cut short. Work an error would leave half done in a way the next function
// could trip over (a macro running in the evaluator, an implementation being stamped) holds
// `gNoResume`, and an error there stops at once, as one outside any `recover` does.
pub var gErrorCount: long = 0;
pub MAX_ERRORS: long = 20;
pub var gNoResume: long = 0;

// Whether a phase may run a function or a declaration under a `recover` of its own now: not
// inside another, whose handler then takes the error, and not past the cap.
pub canRecover -> bool { return !recoverArmed() && gErrorCount < MAX_ERRORS - 1; }

// The end of a phase that went on past its errors: stop if there were any.
pub stopIfErrors -> void {
    if (gErrorCount == 0) { return; }
    if (gErrorCount > 1) { eprintln("{} errors generated.", gErrorCount); }
    flushErr();
    sysExit(COMPILE_FAILED);
}

// A count and its noun, for a message: "1 argument", "3 arguments". Only for the error path, since
// the text is interned and kept.
pub plural n:long noun:str -> str {
    s: String;
    s.pushLong(n);
    s.push(' ');
    s.pushStr(noun);
    if (n != 1) { s.push('s'); }
    return keepString(s);
}

// ─── how an error is printed ─────────────────────────────────────────────────
// The layout gcc and clang use, which editors and terminals already know how to read:
//
//     app.k:12:5: error: mismatched types: expected `u8`, found `long`
//        12 |     c = n;
//           |     ^
//     help: convert it explicitly with `as u8`
//
// The first line of a message is the error. Any line after it is a `note:` or `help:` its caller
// wrote, printed under the source line. An error with no position (a command-line mistake, an
// archive that cannot be read) is just `error: ` and the message.
local printError file:str line:long col:long text:str -> void {
    cut: long = strFind(text, "
").unwrapOr(text.len);
    first: str = strSlice(text, 0, cut);
    if (file.len > 0) {
        eprintln("{}:{}:{}: error: {}", file, line, col, first);
        showSourceLine(file, line, col);
    } else {
        eprintln("error: {}", first);
    }
    if (cut < text.len) { eprintln("{}", strSlice(text, cut + 1, text.len - cut - 1)); }
}

// Line `line` of `file`, with a caret under column `col` (counted from 1). The file is read again,
// which only an error pays for. Nothing is printed when it cannot be read (a module that came out
// of a `.klib` may have no source beside it) or when the line is past its end. A tab before the
// column is copied into the caret line so that the caret lands where a terminal shows the
// character.
pub showSourceLine file:str line:long col:long -> void {
    if (line <= 0 || file == "<input>") { return; }
    hit: Option<str> = tryReadSource(file);
    text: str = "";
    match hit { Some(t) { text = t; } None { return; } }
    at: long = 0;
    n: long = 1;
    while (n < line) {
        nl: long = strFind(strSlice(text, at, text.len - at), "
").unwrapOr(-1);
        if (nl < 0) { return; }
        at = at + nl + 1;
        n = n + 1;
    }
    rest: str = strSlice(text, at, text.len - at);
    end: long = strFind(rest, "
").unwrapOr(rest.len);
    if (end > 0 && charAt(rest, end - 1) == 13) { end = end - 1; }
    src: str = strSlice(rest, 0, end);
    // The line number right-aligned in five columns, as gcc does.
    num: String;
    num.pushLong(line);
    gutter: String;
    if (num.length() < 5) { gutter.pushRepeated(' ', 5 - num.length()); }
    gutter.pushString(num);
    eprintln("{} | {}", gutter, src);
    if (col <= 0) { return; }
    mark: String;
    mark.pushRepeated(' ', gutter.length());
    mark.pushStr(" | ");
    k: long = 0;
    while (k < col - 1 && k < src.len) {
        if (charAt(src, k) == 9) { mark.push('	'); } else { mark.push(' '); }
        k = k + 1;
    }
    mark.push('^');
    eprintln("{}", mark);
}

// Report an error at `gPos` (or with no position when it is 0), then its notes, and either raise to
// the `recover` the phase is running the function under, or stop the compile.
pub fail msg:str -> never {
    nested: bool = gInFail;
    gInFail = true;
    // A call through a function value is taken to write what it is handed (the guard cannot see
    // its callee), and `fail` is handed immutable globals (`fail(USAGE)`), so the hooks get a copy.
    m: str = msg;
    text: String;
    if (nested) { text = stringOf(msg); } else { text = gSpellHook(m); }
    shown: str = "";
    unsafe { shown = text.view(); }
    if (gPos != 0) {
        f: Sym = posFile(gPos);
        where: str = "<input>";
        if (f != NO_SYM) { where = nameOf(f); }
        printError(where, posLine(gPos), posCol(gPos), shown);
    } else {
        printError("", 0, 0, shown);
    }
    if (!nested) { gNoteHook(m); }
    flushErr();
    goOnOrStop(nested);
}

// After an error is printed: count it, and either go on with the next unit of work, by raising
// to the `recover` the phase runs this one under, or stop the compile: when no `recover` is
// armed, when the work in hand would be left half done (`gNoResume`), or at the cap. The raise is
// the phase's own: its `recover` owns every frame down to here, none of them holds a lock, and
// what they leave half built belongs to the unit the phase discards.
local goOnOrStop nested:bool -> never {
    gErrorCount = gErrorCount + 1;
    if (!nested && recoverArmed() && gNoResume == 0 && gErrorCount < MAX_ERRORS) {
        gInFail = false;
        unsafe { raise(); }
    }
    if (gErrorCount >= MAX_ERRORS) { eprintln("error: too many errors, stopping now"); }
    if (gErrorCount > 1) { eprintln("{} errors generated.", gErrorCount); }
    flushErr();
    sysExit(COMPILE_FAILED);
}

// While the parser skips the rest of a declaration it has reported an error in, a lexer error in
// that text is neither printed nor counted: it only raises to the `recover` around the skip, which
// goes on from past it (`Parser.skipToNextDecl`). Only ever set with that `recover` armed.
pub var gQuiet: long = 0;

// An error at a position the caller names rather than at `gPos`: what the lexer and the parser
// report, since they know exactly where they are in the text. A missing file name prints
// `<input>`. The parser reads each declaration under a `recover`, so this goes on to the next
// one as `fail` goes on to the next function.
pub failAt file:str line:long col:long msg:str -> never {
    if (gQuiet > 0 && recoverArmed()) { unsafe { raise(); } }
    where: str = file;
    if (file.len == 0) { where = "<input>"; }
    nested: bool = gInFail;
    gInFail = true;
    m: str = msg;                      // a copy for the hook, as in `fail`
    text: String;
    if (nested) { text = stringOf(msg); } else { text = gSpellHook(m); }
    shown: str = "";
    unsafe { shown = text.view(); }
    printError(where, line, col, shown);
    flushErr();
    goOnOrStop(nested);
}

// `fail` for a message that had to be assembled, almost always by `format`. Takes the String
// rather than a view of it, so the call site is one line and cannot outlive its own buffer.
pub failStr s:String -> never { unsafe { fail(s.view()); } }

pub failAtStr file:str line:long col:long s:String -> never {
    unsafe { failAt(file, line, col, s.view()); }
}
