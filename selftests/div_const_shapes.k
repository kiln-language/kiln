// Division and remainder by constants, formed where the answer goes: into the dividend's own
// register (`n = n / 7`), into another while the dividend lives on, and into a slot when many
// values are live. Every width and sign, dividends either side of zero, powers of two and not.
// A dividend proved never negative drops the rounding toward zero; one whose low bits a test
// put at zero divides by a shift. Through fn values, so nothing folds the arguments in.

q7 x:long -> long { return x / 7; }
r7 x:long -> long { return x % 7; }
q2 x:long -> long { return x / 2; }
r2 x:long -> long { return x % 2; }
q8 x:long -> long { return x / 8; }
r8 x:long -> long { return x % 8; }
q1000 x:long -> long { return x / 1000; }
qmax x:long -> long { return x / 2147483647; }
// The quotient into the dividend's register, then the dividend read no more.
inPlace x:long -> long { n: long = x; n = n / 3; n = n / 5; n = n % 9; return n; }
// The dividend read after the quotient is formed elsewhere.
keeps x:long -> long { q: long = x / 9; r: long = x % 9; return q * 100 + r + x; }
qi x:int -> int { return x / 10; }
ri x:int -> int { return x % 10; }
qs x:i16 -> i16 { return x / 3; }
rs x:i16 -> i16 { return x % 4; }
qc x:char -> char { return x / 5; }
qu x:u32 -> u32 { return x / 7; }
ru x:u32 -> u32 { return x % 16; }
qb x:u8 -> u8 { return x / 3; }
qw x:u64 -> u64 { return x / 10; }
rw x:u64 -> u64 { return x % 1000; }
// Never negative: a square of a counter below a bound, and a counter.
squares n:long -> long { s: long = 0; for i in 0..n { s += (i * i) % 7 + (i * i) / 9; } return s; }
counted n:long -> long { s: long = 0; for i in 0..n { s += i / 3 - i % 5; } return s; }
// The low bit known zero on one side of a test, and not on the other.
halve n:long -> long { if (n % 2 == 0) { return n / 2; } return n / 2 + 1000; }
quarter n:long -> long { if ((n & 3) == 0) { return n / 4; } return 0 - 1; }
// The test was of a value since written again: the division must still round toward zero.
stale n0:long -> long { n: long = n0; if (n % 2 == 0) { n = n + 1; return n / 2; } return 0; }
// A mask wider than the division needs, and one narrower.
wideMask n:long -> long { if ((n & 7) == 0) { return n / 2; } return 1; }
narrowMask n:long -> long { if ((n & 1) == 0) { return n / 4; } return 1; }
// The remainder tested, then read as a number: -3 % 2 is -1, where the mask would say 1.
both x:long -> long { s: long = 0; if (x % 2 == 0) { s = 100; } y: long = x % 2; return s + y; }
// Collatz's step, with the counter used after the loop.
steps n0:long -> long {
    n: long = n0;
    s: long = 0;
    while (n != 1) {
        if (n % 2 == 0) { n = n / 2; } else { n = n * 3 + 1; }
        s += 1;
    }
    return s * 1000 + n;
}
// Many values live at once, so some divisions read or write a slot.
crowd x:long -> long {
    a: long = x / 3; b: long = x / 5; c: long = x / 7; d: long = x / 9; e: long = x / 11;
    f: long = x % 3; g: long = x % 5; h: long = x % 7; i: long = x % 9; j: long = x % 11;
    k: long = x / 13; l: long = x % 13; m: long = x / 17; o: long = x % 17;
    return a + 2 * b + 3 * c + 4 * d + 5 * e + 6 * f + 7 * g + 8 * h + 9 * i + 10 * j + 11 * k + 12 * l + 13 * m + 14 * o;
}

main -> int {
    a: fn(long) -> long = &q7;
    b: fn(long) -> long = &r7;
    if (a(20) != 2 || a(-20) != -2 || a(-1) != 0 || a(-7) != -1 || a(9223372036854775807) != 1317624576693539401) { return 1; }
    if (b(20) != 6 || b(-20) != -6 || b(-7) != 0 || b(0 - 9223372036854775807 - 1) != -1) { return 2; }
    c: fn(long) -> long = &q2;
    d: fn(long) -> long = &r2;
    if (c(7) != 3 || c(-7) != -3 || c(-1) != 0 || d(-7) != -1 || d(7) != 1 || d(-8) != 0) { return 3; }
    e: fn(long) -> long = &q8;
    f: fn(long) -> long = &r8;
    if (e(-17) != -2 || e(17) != 2 || f(-17) != -1 || f(17) != 1) { return 4; }
    g: fn(long) -> long = &q1000;
    h: fn(long) -> long = &qmax;
    if (g(-1999) != -1 || g(1999) != 1 || h(-4294967294) != -2 || h(4294967295) != 2) { return 5; }
    ip: fn(long) -> long = &inPlace;
    kp: fn(long) -> long = &keeps;
    if (ip(1000) != 66 % 9 || ip(-1000) != 0 - 66 % 9 || kp(-100) != -11 * 100 - 1 - 100) { return 6; }
    if (qi(-25) != -2 || ri(-25) != -5 || qi(2147483647) != 214748364) { return 7; }
    if (qs(-32768) != -10922 || rs(-7) != -3) { return 8; }
    lo: long = -128;
    hi: long = 127;
    if (qc(lo as char) as long != -25 || qc(hi as char) as long != 25) { return 9; }
    if (qu(4294967295) != 613566756 || ru(4294967295) != 15) { return 10; }
    top: u64 = ~(0 as u64);
    if (qb(255) != 85 || qw(top) != 1844674407370955161 as u64 || rw(top) != 615) { return 11; }
    if (squares(100) != 36651 || counted(50) != 292) { return 12; }
    hv: fn(long) -> long = &halve;
    qt: fn(long) -> long = &quarter;
    if (hv(-6) != -3 || hv(-7) != 997 || hv(8) != 4 || qt(-12) != -3 || qt(-13) != -1) { return 13; }
    st: fn(long) -> long = &stale;
    if (st(-4) != -1 || st(4) != 2) { return 14; }
    wm: fn(long) -> long = &wideMask;
    nm: fn(long) -> long = &narrowMask;
    if (wm(-8) != -4 || wm(-6) != 1 || nm(-6) != -1 || nm(-8) != -2) { return 15; }
    bt: fn(long) -> long = &both;
    if (bt(-3) != -1 || bt(4) != 100 || bt(5) != 1) { return 16; }
    sp: fn(long) -> long = &steps;
    if (sp(27) != 111001 || sp(1) != 1) { return 17; }
    cr: fn(long) -> long = &crowd;
    if (cr(1000003) != 3672097 || cr(-1000003) != -3672097) { return 18; }
    return 0;
}
