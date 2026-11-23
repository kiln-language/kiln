// Printing: the formatter from `fmt`, aimed at the process's standard streams.
//
// `print`/`println` are the stdout defaults: a `Mutex<BufWriter<Write>>` locked once per call,
// so a whole line is atomic between threads. Everything about how a value is rendered lives in
// `fmt`; what is here is only where the bytes go, and when.
//
// Where stdout goes decides how it buffers, as C's stdio does: to a terminal a line at a time,
// so a person sees each line as it is printed; to a file or a pipe by the block, since a write
// call per println was most of what a program printing a lot spent (400,000 lines: 237 ms of
// CPU a line at a time, 78 by the block). stderr is always a line at a time. Three things keep
// the order what it was: anything on stderr flushes stdout first (C++ ties cerr to cout the same
// way), a panic writes what stdout holds before its message, and a child process starts after
// stdout is flushed. `setStdoutMode` overrides the choice: `BufferMode.Line('\n')` for a log
// someone tails, `Unbuffered` for output interleaving with another writer of the same fd. What
// is held when the program ends some other way is lost, as with C's stdio: killed by a signal,
// or ended with `sysExit` rather than `exit` or a return from `main`.
//
// Every flush bottoms out at `writeAll` (sys.k), so a stdout on a pipe is never truncated.

#include <{fmt, file, sync}>

// ─── default sinks ──────────────────────────────────────────────────────────
// `inner` is a `Write` trait object (a {data, vtable} fat pointer), so it stores the address
// of the leaf. The leaves therefore need their own globals: written inline, the fat pointer
// would name a temporary in the initializer's frame, which is gone before main's body runs.
//
// A leaf held in a global is never dropped, so fd 1 and 2 stay open for the life of the
// process, unlike a `File` local, which closes on drop.
gStdoutFile: File = File { fd: 1 };
gStderrFile: File = File { fd: 2 };

// The SpinLock is not reentrant, so a Display impl must render into the `w` it is handed and
// never call global `print`. The formatter passes `w` down so it can.
var gStdout: Mutex<BufWriter<Write>> = Mutex {
    sl: SpinLock.new(),
    data: BufWriter { inner: gStdoutFile, cap: 4096, pos: 0, mode: BufferMode.Line('\n') }
};
var gStderr: Mutex<BufWriter<Write>> = Mutex {
    sl: SpinLock.new(),
    data: BufWriter { inner: gStderrFile, cap: 4096, pos: 0, mode: BufferMode.Line('\n') }
};

// Format `fmt` with `rest` into one stream, under its lock, and end the line if asked.
local emitTo inout out:Mutex<BufWriter<Write>> fmt:str rest:[any] endLine:bool -> void {
    held: LockGuard;                                 // released at the closing brace
    unsafe { held = out.hold(); }                    // the lock is a global, so it outlives `held`
    writeArgs(out.data, fmt, rest);
    if (endLine) { putChar(out.data, '\n'); }
}

pub print    fmt:str rest:...any -> void { emitTo(&gStdout, fmt, rest, false); }
pub println  fmt:str rest:...any -> void { emitTo(&gStdout, fmt, rest, true); }
pub eprint   fmt:str rest:...any -> void { tieStdout(); emitTo(&gStderr, fmt, rest, false); }
pub eprintln fmt:str rest:...any -> void { tieStdout(); emitTo(&gStderr, fmt, rest, true); }

// Before anything goes to stderr, what stdout holds by the block goes out, so in a file or a
// pipe the two share, stderr never overtakes it. Only when stdout's lock is free: an eprint
// from inside a Display that is printing to stdout would otherwise wait on its own lock. A line
// still held on a terminal stays where it is, as it always did.
local tieStdout -> void {
    unsafe {
        held: Option<LockGuard> = gStdout.tryHold();
        if (held.isSome()) {
            match gStdout.data.mode { Block { gStdout.data.flush(); } _ { } }
        }
    }
}

// At startup: by the block unless stdout is a terminal, and where a panic finds stdout's held
// bytes (sys.k's `spillStdoutNow`) to write them before its message.
@init pickStdoutBuffering -> void {
    if (!isTerminal(1)) { with gStdout { gStdout.data.mode = BufferMode.Block; } }
    unsafe {
        gStdoutBufAt = &gStdout.data.data as long;
        gStdoutPosAt = &gStdout.data.pos as long;
        gStdoutCap = gStdout.data.cap;
    }
}

// A raw byte range straight to stdout, bypassing formatting.
pub unsafe writeBytes ptr:long len:long -> void {
    with gStdout { putBytes(gStdout.data, ptr, len); }
}

// `@fini`: run when `main` returns or the program calls `exit`, so nothing printed is lost.
@fini pub flush -> void { with gStdout { gStdout.data.flush(); } }
pub flushErr -> void { with gStderr { gStderr.data.flush(); } }

// When each stream passes its bytes on. What either holds is flushed first.
pub setStdoutMode m:BufferMode -> void { with gStdout { gStdout.data.setMode(m); } }
pub setStderrMode m:BufferMode -> void { with gStderr { gStderr.data.setMode(m); } }

// Redirection is `unsafe`: the new sink is a borrowed view stored in a global, so the caller
// vouches that it outlives the redirection window.
pub unsafe getStdout -> Write { return gStdout.data.inner; }
pub unsafe setStdout w:Write -> void { gStdout.data.flush(); gStdout.data.inner = w; gStdoutPosAt = 0; }   // a panic leaves someone else's sink alone
pub unsafe getStderr -> Write { return gStderr.data.inner; }
pub unsafe setStderr w:Write -> void { gStderr.data.flush(); gStderr.data.inner = w; }
