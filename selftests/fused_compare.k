// A value computed only for the branch after it is never written: `x & m` tested against zero
// is `test x, m`, a load compared with something is `cmp [p], b` at the load's width, and a
// quotient or remainder is compared where the division leaves it. Every width and signedness,
// masks with the type's sign bit, operands in registers and in slots, a global base.
#include <stdlib::vec>

var gWords: [long; 4] = [5, -6, 7, -8];
var gBytes: [u8; 4] = [1, 200, 128, 0];

anyBit x:long m:long -> long { if ((x & m) != 0) { return 1; } return 0; }
lowBit x:long -> long { if ((x & 1) == 0) { return 1; } return 0; }
notTwo x:long -> long { if ((x & -2) != 0) { return 1; } return 0; }
signBit x:long -> long { m: long = 0 - 9223372036854775807 - 1; if ((x & m) < 0) { return 1; } return 0; }
intMask x:int -> long { if ((x & -2) == 0) { return 1; } return 0; }
intSign x:int -> long { if ((x & (0 - 2147483647 - 1) as int) < 0) { return 1; } return 0; }
byteTop x:u8 -> long { if ((x & 128) != 0) { return 1; } return 0; }
charTop x:char -> long { m: long = -128; if ((x & m as char) != 0) { return 1; } return 0; }
shortTop x:i16 -> long { if ((x & -32768 as i16) < 0) { return 1; } return 0; }
wordTop x:u32 -> long { m: u32 = 2147483648; if ((x & m) != 0) { return 1; } return 0; }
flag b:bool -> long { if (b) { return 1; } return 0; }

// Loads compared at their width.
countAbove xs:[u8] lim:u8 -> long { n: long = 0; for i in 0..xs.len { if (xs[i] > lim) { n += 1; } } return n; }
countBelowC xs:[char] -> long { n: long = 0; for i in 0..xs.len { if (xs[i] < -100 as char) { n += 1; } } return n; }
countShort xs:[i16] lim:i16 -> long { n: long = 0; for i in 0..xs.len { if (xs[i] >= lim) { n += 1; } } return n; }
countInt xs:[int] -> long { n: long = 0; for i in 0..xs.len { if (xs[i] != -1) { n += 1; } } return n; }
countU32 xs:[u32] lim:u32 -> long { n: long = 0; for i in 0..xs.len { if (xs[i] < lim) { n += 1; } } return n; }
countLong xs:[long] lim:long -> long { n: long = 0; for i in 0..xs.len { if (xs[i] <= lim) { n += 1; } } return n; }
countU64 xs:[u64] lim:u64 -> long { n: long = 0; for i in 0..xs.len { if (xs[i] > lim) { n += 1; } } return n; }
// A byte compared as a wider signed value: the load's own signedness is not the comparison's.
wideByte xs:[u8] -> long { n: long = 0; for i in 0..xs.len { if (xs[i] as long > 100) { n += 1; } } return n; }
countBool xs:[bool] -> long { n: long = 0; for i in 0..xs.len { if (xs[i]) { n += 1; } } return n; }
globals -> long {
    n: long = 0;
    if (gWords[1] < 0) { n += 1; }
    if (gWords[2] == 7) { n += 10; }
    if (gBytes[1] > 150) { n += 100; }
    for i in 0..4 { if (gBytes[i] == 0) { n += 1000; } }
    return n;
}
// The other operand spilled: many values live across the comparisons.
crowded xs:[long] -> long {
    a: long = xs[0] + 1; b: long = xs[1] + 2; c: long = xs[2] + 3; d: long = xs[3] + 4;
    e: long = a * b; f: long = c * d; g: long = a + c; h: long = b + d; k: long = e - f;
    n: long = 0;
    for i in 0..xs.len {
        if (xs[i] > a) { n += 1; }
        if (xs[i] < h) { n += 2; }
        if (xs[i] == k) { n += 4; }
    }
    return n + a + b + c + d + e + f + g + h + k;
}
// Divisions compared where they are formed.
remIs x:long -> long { if (x % 7 == 3) { return 1; } if (x % 7 == -3) { return 2; } return 0; }
quotBig x:long -> long { if (x / 1000 > 5) { return 1; } return 0; }
divides n:long d:long -> long { if (n % d == 0) { return 1; } return 0; }
quotAgainst x:long y:long -> long { if (x / 3 < y) { return 1; } return 0; }
narrowRem x:int -> long { if (x % 5 != 0) { return 1; } return 0; }

main -> int {
    ab: fn(long, long) -> long = &anyBit;
    lb: fn(long) -> long = &lowBit;
    nt: fn(long) -> long = &notTwo;
    sb: fn(long) -> long = &signBit;
    im: fn(int) -> long = &intMask;
    isg: fn(int) -> long = &intSign;
    bt: fn(u8) -> long = &byteTop;
    ct: fn(char) -> long = &charTop;
    st: fn(i16) -> long = &shortTop;
    wt: fn(u32) -> long = &wordTop;
    fl: fn(bool) -> long = &flag;
    if (ab(12, 4) != 1 || ab(12, 3) != 0 || ab(-1, 0 - 9223372036854775807 - 1) != 1) { return 1; }
    if (lb(-4) != 1 || lb(-3) != 0 || nt(1) != 0 || nt(-1) != 1 || nt(2) != 1) { return 2; }
    if (sb(-5) != 1 || sb(5) != 0) { return 3; }
    if (im(1) != 1 || im(-1) != 0 || isg(-7) != 1 || isg(7) != 0) { return 4; }
    if (bt(200) != 1 || bt(127) != 0) { return 5; }
    lo: long = -5;
    hi: long = 5;
    if (ct(lo as char) != 1 || ct(hi as char) != 0) { return 6; }
    if (st(-3 as i16) != 1 || st(3 as i16) != 0) { return 7; }
    if (wt(4294967295) != 1 || wt(2147483647) != 0) { return 8; }
    if (fl(true) != 1 || fl(false) != 0) { return 9; }
    ca: fn([u8], u8) -> long = &countAbove;
    wb: fn([u8]) -> long = &wideByte;
    bs: [u8; 5] = [0, 99, 100, 101, 255];
    if (ca(bs[..], 100) != 2 || ca(bs[..], 0) != 4 || wb(bs[..]) != 2) { return 10; }
    cb: fn([char]) -> long = &countBelowC;
    m100: long = -100;
    cs: [char; 4] = [-128 as char, m100 as char, -101 as char, 127 as char];
    if (cb(cs[..]) != 2) { return 11; }
    cs2: fn([i16], i16) -> long = &countShort;
    ss: [i16; 4] = [-32768 as i16, -1 as i16, 0 as i16, 32767 as i16];
    if (cs2(ss[..], -1 as i16) != 3) { return 12; }
    ci: fn([int]) -> long = &countInt;
    is: [int; 4] = [-1, 0, -2147483647, 2147483647];
    if (ci(is[..]) != 3) { return 13; }
    cu: fn([u32], u32) -> long = &countU32;
    us: [u32; 4] = [0, 2147483648, 4294967295, 7];
    if (cu(us[..], 2147483648) != 2 || cu(us[..], 4294967295) != 3) { return 14; }
    cl: fn([long], long) -> long = &countLong;
    ls: [long; 4] = [-9, 0, 9, 9223372036854775807];
    if (cl(ls[..], 0) != 2 || cl(ls[..], -10) != 0) { return 15; }
    cw: fn([u64], u64) -> long = &countU64;
    top: u64 = ~(0 as u64);
    ws: [u64; 3] = [0, top, 9223372036854775808];
    if (cw(ws[..], 9223372036854775807) != 2) { return 16; }
    cbo: fn([bool]) -> long = &countBool;
    fs: [bool; 4] = [true, false, true, true];
    if (cbo(fs[..]) != 3) { return 17; }
    gl: fn() -> long = &globals;
    if (gl() != 1111) { return 18; }
    cr: fn([long]) -> long = &crowded;
    xs: [long; 6] = [3, -4, 10, 2, 7, -100];
    if (cr(xs[..]) != 36) { return 19; }
    ri: fn(long) -> long = &remIs;
    qb: fn(long) -> long = &quotBig;
    if (ri(10) != 1 || ri(-10) != 2 || ri(11) != 0 || qb(6000) != 1 || qb(-6000) != 0) { return 20; }
    dv: fn(long, long) -> long = &divides;
    if (dv(12, 4) != 1 || dv(12, 5) != 0 || dv(-12, 4) != 1 || dv(5000000000, 5) != 1 || dv(12, 5000000000) != 0) { return 21; }
    qa: fn(long, long) -> long = &quotAgainst;
    if (qa(-7, -1) != 1 || qa(-7, -2) != 0 || qa(9, 3) != 0) { return 22; }
    nr: fn(int) -> long = &narrowRem;
    if (nr(-10) != 0 || nr(-11) != 1) { return 23; }
    return 0;
}
