// A value that lives in `rax` from the instruction that writes it to the one after, which reads
// it: a call's result, and what a return or the next call's first argument is computed from.
// Each reader has to take the value before anything else it fetches goes through `rax`. The
// callees have a loop and several callers, so they stay calls.

var gKeep: long = 0;

tri n:long -> long {
    s: long = 0;
    for i in 0..n { s += i; }
    return s + n;
}
tri32 n:int -> int {
    s: int = 0;
    for i in 0..n { s += i as int; }
    return s + n;
}
low8 n:long -> u8 {
    s: u8 = 0;
    for i in 0..n { s += 50; }
    return s;
}
pair a:long b:long -> long {
    s: long = 0;
    for i in 0..1 { s += a * 10; }
    return s + b;
}
at p:*long n:long -> *long {
    q: *long = p;
    for i in 0..n { unsafe { q = q + 1; } }
    return q;
}
big a0:long a1:long a2:long a3:long a4:long a5:long a6:long a7:long a8:long a9:long a10:long a11:long -> long {
    s: long = 0;
    for i in 0..1 { s += a0 * 1000 + a11 * 100 + a10 * 10 + a1; }
    return s;
}
mixf a:long x:f64 -> long {
    s: long = 0;
    for i in 0..1 { s += a * 10 + (x as long); }
    return s;
}

ret1 n:long -> long { return tri(n); }
subR a:long n:long -> long { return a - tri(n); }
subFromConst n:long -> long { return 1000 - tri(n); }
addL n:long k:long -> long { return tri(n) + k * 2; }
mulBoth n:long -> long { return tri(n) * tri(n + 1); }
wrap32 n:int -> int { return tri32(n) + 2147483640; }
lowPlus n:long -> long { return (low8(n) + 10) as long; }
nested n:long -> long { return tri(tri(n)); }
nested2 n:long -> long { return pair(tri(n - 1), 5); }
isTen n:long -> long { if (tri(n) == 10) { return 1; } return 0; }
keepIt n:long -> void { gKeep = tri(n); }
through p:*long n:long -> long { unsafe { return *at(p, n); } }
pickOf xs:[long] n:long -> long { return xs[tri(n)]; }
bigCall n:long -> long { return big(tri(n), 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12); }
// The same with nothing computed between the two calls: two arguments go on the stack, through
// `rax`, so the first call's result may not wait there.
bigCall2 n:long a:long b:long c:long d:long e:long f:long g:long h:long i:long j:long k:long -> long {
    return big(tri(n), a, b, c, d, e, f, g, h, i, j, k);
}
floatCall n:long -> long { return mixf(tri(n), 2.5); }
via f:fn(long) -> long n:long -> long { return f(n) - 1; }

main -> int {
    if (ret1(4) != 10 || subR(100, 4) != 90 || subFromConst(4) != 990) { return 1; }
    if (addL(4, 3) != 16 || mulBoth(3) != 60) { return 2; }
    if (wrap32(4) != -2147483646) { return 3; }
    if (lowPlus(5) != 4) { return 4; }
    if (nested(3) != 21 || nested2(4) != 65) { return 5; }
    if (isTen(4) != 1 || isTen(3) != 0) { return 6; }
    keepIt(10);
    if (gKeep != 55) { return 7; }
    xs: [long; 12] = [0, 10, 20, 30, 40, 50, 60, 70, 80, 90, 100, 110];
    unsafe { if (through(&xs[0], 3) != 30) { return 8; } }
    if (pickOf(xs[..], 3) != 60) { return 9; }
    if (bigCall(4) != 11312) { return 10; }
    if (floatCall(4) != 102) { return 11; }
    if (via(&tri, 4) != 9) { return 12; }
    // The same bodies through fn values, each emitted on its own: its value returned from `rax`.
    f1: fn(long) -> long = &ret1;
    f2: fn(long, long) -> long = &subR;
    f3: fn(long) -> long = &subFromConst;
    f4: fn(long, long) -> long = &addL;
    f5: fn(long) -> long = &mulBoth;
    f6: fn(int) -> int = &wrap32;
    f7: fn(long) -> long = &lowPlus;
    f8: fn(long) -> long = &nested;
    f9: fn(long) -> long = &nested2;
    f10: fn(long) -> long = &isTen;
    f11: fn([long], long) -> long = &pickOf;
    f12: fn(long) -> long = &bigCall;
    f13: fn(long) -> long = &floatCall;
    if (f1(4) != 10 || f2(100, 4) != 90 || f3(4) != 990 || f4(4, 3) != 16 || f5(3) != 60) { return 13; }
    if (f6(4) != -2147483646 || f7(5) != 4 || f8(3) != 21 || f9(4) != 65 || f10(4) != 1) { return 14; }
    if (f11(xs[..], 3) != 60 || f12(4) != 11312 || f13(4) != 102) { return 15; }
    f14: fn(long, long, long, long, long, long, long, long, long, long, long, long) -> long = &bigCall2;
    if (f14(4, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12) != 11312) { return 16; }
    return 0;
}
