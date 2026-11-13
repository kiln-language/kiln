// What a trap should have said.
//
// A failed bounds check, a missing key, an unwrapped `None` — every one of these used to be a
// bare `ud2`, which reaches the shell as SIGILL and says nothing at all: not which check
// failed, not with what value, not in which container. The program still dies, and still dies
// immediately, but now it says why first.
//
// Self-contained on purpose. It formats its own numbers rather than calling `io`, because the
// containers that need it (`vec`, `map`, `deque`, `pool`) sit below the formatter and must not
// have to drag it in — and because a panic must work when nothing else is trustworthy: it
// touches no allocator, no buffered sink, and no global.
//
// The three entry points are known to the compiler by name: a call to one ends its path, so a
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
        i = i - 1;
        buf[i] = ('0' - n % 10) as u8;
        n = n / 10;
        if (n == 0) { break; }
    }
    if (v < 0) {
        i = i - 1;
        buf[i] = '-';
    }
    emit(buf[i..] as str);
}

// Report `msg` and abort. `@panic`: what `assert!` calls when it fails.
@panic pub panic msg:str -> never {
    emit("panic: ");
    emit(msg);
    emit("\n");
    sysExit(aborted);
}

// The shape almost every container trap has: something was asked for a position it does not
// have. `what` names the operation, so the line reads as e.g.
//   panic: Vec.get: index 7 out of range, length 3
pub panicIndex what:str i:long n:long -> never {
    emit("panic: ");
    emit(what);
    emit(": index ");
    emitLong(i);
    emit(" out of range, length ");
    emitLong(n);
    emit("\n");
    sysExit(aborted);
}

// A value that was asked for the wrong thing — an unwrapped `None`, an `Err` read as `Ok`,
// a stale handle. `what` names the operation, `saw` what was actually there.
//   panic: Option.unwrap: called on None
pub panicState what:str saw:str -> never {
    emit("panic: ");
    emit(what);
    emit(": ");
    emit(saw);
    emit("\n");
    sysExit(aborted);
}
