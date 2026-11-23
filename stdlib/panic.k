// Panics: say what failed on stderr, then exit with SIGABRT's status.
//
// Every runtime check in the containers ends here (a failed bounds check, a missing key, an
// unwrapped `None`), and the message names the operation and the values involved.
//
// Self-contained. It formats its own numbers instead of calling `io`, because the containers
// that use it (`vec`, `map`, `deque`, `pool`) sit below the formatter and must not pull it in.
// A panic also has to work when nothing else can be trusted, so it touches no allocator and no
// buffered sink of its own. What it reads beyond its arguments is where io said stdout's held
// bytes are (sys.k's `spillStdoutNow`), to write them before the message: into a file or a pipe
// stdout buffers by the block, and what was printed before a crash should not be lost with it.
//
// The compiler knows the three entry points by name: a call to one ends its path, so a
// function whose last statement is a panic needs no `return` after it.
#include <sys>

// SIGABRT's exit status. A shell testing for a crash still sees one, and it is distinct from
// any status a program is likely to return deliberately.
local aborted: long = 134;

// A `str` always carries a length that matches its bytes, so writing one is safe.
local emit s:str -> void {
    if (s.len > 0) { unsafe { sysWrite(2, s.ptr, s.len); } }
}

// `v` in decimal, into fd 2. Negatives print with a sign; the digits are built backwards into
// a stack buffer, which is why there is no allocation anywhere in this file.
local emitLong v:long -> void {
    buf: [u8; 24];
    i: long = 24;
    n: long = v;
    if (n > 0) { n = -n; }               // work in the negative domain: it reaches long's minimum
    loop {
        i -= 1;
        buf[i] = ('0' - n % 10) as u8;
        n /= 10;
        if (n == 0) { break; }
    }
    if (v < 0) {
        i -= 1;
        buf[i] = '-';
    }
    emit(buf[i..] as str);
}

// Report `msg` and abort. `@panic`: what `assert!` calls when it fails.
@panic pub panic msg:str -> never {
    spillStdoutNow();
    emit("panic: ");
    emit(msg);
    emit("\n");
    sysExit(aborted);
}

// The shape almost every container trap has: something was asked for a position it does not
// have. `what` names the operation, so the line reads as e.g.
//   panic: Vec.get: index 7 out of range for length 3
pub panicIndex what:str i:long n:long -> never {
    spillStdoutNow();
    emit("panic: ");
    emit(what);
    emit(": index ");
    emitLong(i);
    emit(" out of range for length ");
    emitLong(n);
    emit("\n");
    sysExit(aborted);
}

// An operation that cannot go ahead on the value it was given: an unwrapped `None`, an `Err`
// read as `Ok`, a stale handle. `what` names the operation and `saw` says what was wrong.
//   panic: Option.unwrap: called on a None value
pub panicState what:str saw:str -> never {
    spillStdoutNow();
    emit("panic: ");
    emit(what);
    emit(": ");
    emit(saw);
    emit("\n");
    sysExit(aborted);
}
