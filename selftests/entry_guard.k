// A function that begins `if (test) { return ...; }` makes that test before its prologue, reading
// each parameter where it arrived, and returns from there with no frame to take down. Each one
// below keeps something across a call, so it has a prologue for the early return to skip, and
// each is called through a fn value, so nothing is copied into `main`.

var gCount: long = 0;
var gLimit: long = 6;
var gTotal: long = 0;
bump x:long -> long { gCount = gCount + 1; return x; }

// The comparison, turned round for the jump to the early return, on each kind of operand.
fibg n:long -> long {
    if (n < 2) { return n; }
    return fibg(n - 1) + fibg(n - 2);
}
ucount x:u32 -> long {
    if (x < 3) { return x as long; }
    return bump(1) + ucount(x - 1);
}
s16 x:i16 -> long {
    if (x <= -5) { return -100; }
    return bump(x as long) + s16((x - 1) as i16);
}
// `x + 1` wraps at eight bits, so the recursion ends at 255 + 1.
u8w x:u8 -> long {
    if (x == 0) { return 1000; }
    return bump(x as long) + u8w(x + 1);
}
// A bool tested as it is, in both senses.
whenNot b:bool x:long -> long {
    if (!b) { return x; }
    return bump(x) * 2 + whenNot(false, x + 1);
}
whenSo b:bool x:long -> long {
    if (b) { return x; }
    return bump(x) * 2 + whenSo(true, x + 1);
}
// What is returned: the second parameter, or a constant.
retSecond a:long b:long -> long {
    if (a == 0) { return b; }
    return bump(a) + retSecond(a - 1, b + 1);
}
retConst a:long b:long -> long {
    if (a == b) { return 77; }
    return bump(a) + retConst(a + 1, b);
}
// The test reads through a borrow, and a global.
struct Buf { len: long, cap: long }
emptyLen b:&Buf k:long -> long {
    if (b.len == 0) { return k; }
    return bump(b.len) + k * 10;
}
overLimit n:long -> long {
    if (n > gLimit) { return -1; }
    return bump(n) + overLimit(n + 1);
}
// A value the test loads, with three parameters arriving in `rax`, `rbx` and `rcx`: it is held
// in a register none of them arrives in, so `k` and `n` are still there when the test fails.
lenGuard b:&Buf k:long n:long -> long {
    if (b.len == n) { return k; }
    return 1 + lenGuard(b, k + 10, n + 1);
}
// What the test computed is read again after it, so the test stays where it was.
reuse b:&Buf -> long {
    t: long = b.len * 2;
    if (t == 0) { return 0; }
    return bump(t) + t;
}
// Nothing to return.
addUp n:long -> void {
    if (n == 0) { return; }
    gTotal = gTotal + bump(n);
    addUp(n - 1);
}
// Floats around the test: an `xmm` argument has to be where it arrived when the test fails.
fmix x:f64 n:long y:f64 -> long {
    if (n <= 0) { return n; }
    return (x as long) + bump(n) + fmix(x + 1.0, n - 1, y) + (y as long);
}
// Twelve parameters, the last two on the stack.
wide a0:long a1:long a2:long a3:long a4:long a5:long a6:long a7:long a8:long a9:long a10:long a11:long -> long {
    if (a0 == 0) { return a11 * 100 + a10; }
    return bump(a1) + wide(a0 - 1, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10 + 1, a11 + 2);
}
// The early return is the branch's target, not the fall-through.
targetExit n:long -> long {
    if (n >= 2) {
        a: long = bump(n);
        return a + targetExit(n - 1);
    }
    return n * 3;
}
// A tail call turned into a jump back to the top.
gcd a:long b:long -> long {
    if (b == 0) { return a; }
    return gcd(b, bump(a % b));
}

main -> int {
    f1: fn(long) -> long = &fibg;
    if (f1(20) != 6765 || f1(1) != 1 || f1(-3) != -3) { return 1; }
    f2: fn(u32) -> long = &ucount;
    if (f2(10) != 10 || f2(2) != 2 || f2(0) != 0) { return 2; }
    f3: fn(i16) -> long = &s16;
    if (f3(3) != -104 || f3(-5) != -100 || f3(-32768 as i16) != -100) { return 3; }
    f4: fn(u8) -> long = &u8w;
    if (f4(250) != 2515 || f4(0) != 1000) { return 4; }
    f5: fn(bool, long) -> long = &whenNot;
    f6: fn(bool, long) -> long = &whenSo;
    if (f5(false, 4) != 4 || f5(true, 4) != 13 || f6(true, 4) != 4 || f6(false, 4) != 13) { return 5; }
    f7: fn(long, long) -> long = &retSecond;
    f8: fn(long, long) -> long = &retConst;
    if (f7(3, 10) != 19 || f7(0, 5) != 5 || f8(4, 4) != 77 || f8(1, 3) != 80) { return 6; }
    e: Buf = Buf { len: 0, cap: 4 };
    g: Buf = Buf { len: 3, cap: 4 };
    f9: fn(&Buf, long) -> long = &emptyLen;
    if (f9(&e, 7) != 7 || f9(&g, 7) != 73) { return 7; }
    f10: fn(long) -> long = &overLimit;
    if (f10(4) != 14 || f10(9) != -1) { return 8; }
    f17: fn(&Buf, long, long) -> long = &lenGuard;
    if (f17(&g, 5, 0) != 38 || f17(&g, 5, 3) != 5) { return 15; }
    f11: fn(&Buf) -> long = &reuse;
    if (f11(&e) != 0 || f11(&g) != 12) { return 9; }
    f12: fn(long) -> void = &addUp;
    f12(4);
    f12(0);
    if (gTotal != 10) { return 10; }
    f13: fn(f64, long, f64) -> long = &fmix;
    if (f13(1.5, 2, 3.25) != 12 || f13(1.5, 0, 3.25) != 0) { return 11; }
    f14: fn(long, long, long, long, long, long, long, long, long, long, long, long) -> long = &wide;
    if (f14(2, 5, 0, 0, 0, 0, 0, 0, 0, 0, 1, 7) != 1113 || f14(0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 9) != 904) { return 12; }
    f15: fn(long) -> long = &targetExit;
    if (f15(4) != 12 || f15(1) != 3 || f15(-2) != -6) { return 13; }
    f16: fn(long, long) -> long = &gcd;
    if (f16(84, 36) != 12 || f16(7, 0) != 7) { return 14; }
    return 0;
}
