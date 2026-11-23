#include <stdlib::{atomic, mem}>

// What a callee may change includes what its code writes without naming it (relax.k,
// `implicitRegs`): `rep movsb` (rdi, rsi, rcx), `rep stosb` in `memset` (rdi, rcx), a shift by a
// variable (rcx), a division (rax, rdx), `cmpxchg` (rax), `syscall` (rcx and r11, the kernel's),
// the float scratch, and what an early return written out of line computes (`emitGuard`, the
// sum in r8: six arguments arrive in rax to rsi), and the registers a call's own arguments are
// passed in, which `wide` never reads; and floats, which `fmix` computes in the first `xmm`
// registers while `fkeep` holds five across its calls, more than the ones it leaves alone hold.
// Each callee below is small and leaves most registers alone; the caller
// keeps a dozen values across a call to each, so some sit in caller-saved registers across it,
// and every one must come back. Each callee has a loop, so it stays a call.

var gSink: long = 0;
var gA: [u8; 64];
var gB: [u8; 64];
var gW: long = 0;

copier n:long -> long {
    s: long = n;
    for i in 0..(n & 1) + 1 { s = s + i; }
    unsafe { memcpy(&gA as long, &gB as long, n & 63); }
    return s + 1;
}
setter n:long -> long {
    s: long = n;
    for i in 0..(n & 1) + 1 { s = s + i; }
    unsafe { memset(&gB as long, n & 127, (n & 31) + 1); }
    return s + 2;
}
shifter x:long n:long -> long {
    s: long = x;
    for i in 0..(n & 1) + 1 { s = s + i; }
    return (s << (n & 15)) + (x >> (n & 7));
}
divider x:long y:long -> long {
    s: long = x;
    for i in 0..(y & 1) + 1 { s = s + i; }
    return s / (y | 1) + x % (y | 3);
}
swapper n:long -> long {
    s: long = n;
    for i in 0..(n & 1) + 1 { s = s + i; }
    old: long = 0;
    unsafe { old = atomicCas(&gW as *long, gW, s); }
    return old + n;
}
sys n:long -> long {
    s: long = n;
    for i in 0..(n & 1) + 1 { s = s + i; }
    r: long = 0;
    unsafe { r = syscall(39); }      // getpid
    return s + (r & 1) - (r & 1);
}
floaty n:long -> long {
    s: long = n;
    for i in 0..(n & 1) + 1 { s = s + i; }
    a: f64 = s as f64;
    b: f64 = a * 1.5 + 0.25;
    c: f64 = b / (a + 1.0);
    return (c * 100.0) as long;
}
// The test and its return are written before the prologue, the return with the cold text.
early a:long b:long c:long d:long e:long f:long -> long {
    if (a + b > 1000) { x: long = a * 3 + c; return x ^ b; }
    s: long = shifter(a, b);
    for i in 0..(b & 1) + 1 { s = s + i; }
    return s + f;
}
// Reads its first argument only: what the caller writes into r8 to r11 for the others is the
// call's to change, not the callee's.
wide a:long b:long c:long d:long e:long f:long g:long h:long i:long j:long -> long {
    s: long = a;
    for x in 0..(a & 1) + 1 { s = s + x; }
    return s;
}
fmix x:f64 y:f64 -> f64 {
    s: f64 = x * 1.5 + y;
    for i in 0..(gSink & 1) + 1 { s = s + 0.5; }
    return s;
}
fkeep k:long -> long {
    f1: f64 = (gSink + k) as f64 + 0.5;
    f2: f64 = f1 * 2.0;
    f3: f64 = f1 + 3.25;
    f4: f64 = f2 - 1.5;
    f5: f64 = f3 * f4;
    r: f64 = fmix(f1, f2);
    r = r + fmix(f3, f4) + f1 + f2 * 2.0 + f3 * 3.0 + f4 * 4.0 + f5 * 5.0;
    return (r * 4.0) as long;
}

keep k:long -> long {
    v1: long = gSink + k + 1; v2: long = gSink + k * 2 + 2; v3: long = gSink + k * 3 + 3;
    v4: long = gSink + k * 4 + 4; v5: long = gSink + k * 5 + 5; v6: long = gSink + k * 6 + 6;
    v7: long = gSink + k * 7 + 7; v8: long = gSink + k * 8 + 8; v9: long = gSink + k * 9 + 9;
    v10: long = gSink + k * 10 + 10; v11: long = gSink + k * 11 + 11; v12: long = gSink + k * 12 + 12;
    r: long = copier(k);
    r = r + v1 + v2 * 2;
    r = r + setter(k) + v3 * 3;
    r = r + shifter(r & 255, k) + v4 * 4;
    r = r + divider(r, k) + v5 * 5;
    r = r + swapper(k) + v6 * 6;
    r = r + sys(k) + v7 * 7;
    r = r + floaty(k) + v8 * 8;
    r = r + early(k * 300, k * 200, 1, 2, 3, 4) + v9;
    r = r + wide(k, 1, 2, 3, 4, 5, 6, 7, 8, 9) + v10;
    r = r + fkeep(k & 7) + v11;
    r = r & 16777215;
    return r + v1 + v2 + v3 + v4 + v5 + v6 + v7 + v8 + v9 * 9 + v10 * 10 + v11 * 11 + v12 * 12;
}

// A second caller of each, so none is copied into `keep`.
again k:long -> long { return copier(k) + setter(k) + shifter(k, k + 1) + divider(k, k + 1) + swapper(k) + sys(k) + floaty(k) + early(k, k, 1, 2, 3, 4) + wide(k, 9, 8, 7, 6, 5, 4, 3, 2, 1) + fkeep(k) + (fmix(1.0, 2.0) as long); }

main -> long {
    gSink = copier(0) - 1;
    if (again(1) != 451) { return 9; }
    if (keep(5) != 15281) { return 1; }
    if (keep(12) != 942137) { return 2; }
    if (keep(37) != 73797) { return 3; }
    return 0;
}
