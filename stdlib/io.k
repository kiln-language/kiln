// Printing: the formatter from `fmt`, aimed at the process's standard streams.
//
// `print`/`println` are the stdout defaults — a `Mutex<BufWriter<Write>>` locked once per call,
// so a whole line is atomic between threads. Everything about how a value is RENDERED lives in
// `fmt`; what is here is only where the bytes go, and when.
//
// Both streams start line-buffered on '\n'. `setStdoutMode` changes that — `BufferMode.Block`
// for a program whose output goes to a file or a pipe and should cost as few syscalls as
// possible, `Unbuffered` for one interleaving with something else that writes the same fd.
//
// Every flush bottoms out at `writeAll` (sys.k), so a stdout on a pipe is never truncated.

#include <{fmt, file, sync}>

// ─── default sinks ──────────────────────────────────────────────────────────
// `inner` is a `Write` TRAIT OBJECT — a {data, vtable} fat pointer — so it stores the ADDRESS
// of the leaf. The leaves therefore need their own globals: written inline, the fat pointer
// would name a temporary in the initializer's frame, which is gone before main's body runs.
//
// A leaf held in a global is never dropped, so fd 1 and 2 stay open for the life of the
// process — unlike a `File` local, which closes on drop.
gStdoutFile: File = File { fd: 1 };
gStderrFile: File = File { fd: 2 };

// The SpinLock is not reentrant, so a Display impl must render into the `w` it is handed and
// never call global `print`; the formatter passes `w` down for exactly that reason.
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
    held: LockGuard = out.hold();
    writeArgs(out.data, fmt, rest);
    if (endLine) { putChar(out.data, '\n'); }
}

pub print    fmt:str rest:...any -> void { emitTo(&gStdout, fmt, rest, false); }
pub println  fmt:str rest:...any -> void { emitTo(&gStdout, fmt, rest, true); }
pub eprint   fmt:str rest:...any -> void { emitTo(&gStderr, fmt, rest, false); }
pub eprintln fmt:str rest:...any -> void { emitTo(&gStderr, fmt, rest, true); }

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
pub unsafe setStdout w:Write -> void { gStdout.data.flush(); gStdout.data.inner = w; }
pub unsafe getStderr -> Write { return gStderr.data.inner; }
pub unsafe setStderr w:Write -> void { gStderr.data.flush(); gStderr.data.inner = w; }
