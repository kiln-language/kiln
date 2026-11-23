// An `if` whose arms only compute the value one variable gets is written as conditional moves:
// both arms run, and `cmov` keeps the one the condition chose. Each arm in turn written in place,
// moved in through rax, computed before the comparison (an arm of one instruction that sets the
// flags), or moved straight from the register it copies (and not, where the other arm reuses
// that register); values an arm computes for itself; narrow types that wrap; signed, unsigned and
// bool conditions, and one fused with a mask or a load; `&&` and `||`, whose second arm is entered
// twice and stays a branch. Then the one-armed shape with several values, with a value the arm
// computes for itself, and with a value read again after the arm wrote it. Every body is called
// through a fn value, so it stays in its own function, and every case is checked both ways.

// A collatz step: one arm a shift (it sets the flags, so it goes before the comparison), the
// other two `lea`s.
step n:long -> long { r: long = 0; if (n % 2 == 0) { r = n / 2; } else { r = n * 3 + 1; } return r; }
steps n0:long -> long {
    n: long = n0;
    s: long = 0;
    while (n != 1) {
        if (n % 2 == 0) { n = n / 2; } else { n = n * 3 + 1; }
        s += 1;
    }
    return s;
}
// Copies and constants.
pick a:long b:long c:bool -> long { r: long = 0; if (c) { r = a; } else { r = b; } return r; }
pickConst x:long -> long { r: long = 0; if (x > 5) { r = 7; } else { r = -3; } return r; }
pickMixed a:long x:long -> long { r: long = 0; if (x != 0) { r = a; } else { r = 12; } return r; }
// A copy whose source dies in its arm, while the other arm's own value lands in that register:
// the copy then goes through rax, not straight from the register.
copyClash a:long b:long c:bool -> long {
    s: long = a ^ b;
    r: long = 0;
    if (c) { r = s; } else { t: long = a * 5; r = t + b; }
    k: long = 0;
    if (c) { k = 1; }
    return r * 100 + a + b + k;
}
// `&&` and `||`: the second arm is also entered from the first test, so it stays a branch.
both a:long b:long -> long { r: long = 0; if (a > 0 && b > 0) { r = a + 1; } else { r = b + 2; } return r; }
either a:long b:long -> long { r: long = 0; if (a > 0 || b > 0) { r = a + 1; } else { r = b + 2; } return r; }
// Both arms leave the flags alone, and one computes a value of its own first.
sumOrProd a:long b:long c:bool -> long { r: long = 0; if (c) { r = a + b; } else { r = a * 3; } return r; }
withLocal a:long b:long -> long { r: long = 0; if (a < b) { t: long = a * 5; r = t + b; } else { r = b - 4; } return r; }
// One arm sets the flags, on either side.
maskOrAdd x:long c:bool -> long { r: long = 0; if (c) { r = x & 15; } else { r = x + 2; } return r; }
addOrMask x:long c:bool -> long { r: long = 0; if (c) { r = x + 2; } else { r = x & 15; } return r; }
xorOrShift x:long y:long -> long { r: long = 0; if (x >= y) { r = x ^ y; } else { r = y << 2; } return r; }
// Narrow values wrap at their width in both arms.
narrowU8 a:u8 b:u8 -> u8 { r: u8 = 0; if (a > b) { r = a + 200; } else { r = b * 3; } return r; }
narrowI16 a:i16 b:i16 -> i16 { r: i16 = 0; if (a < b) { r = a - 30000; } else { r = b << 2; } return r; }
narrowInt a:int -> int { r: int = 0; if (a >= 0) { r = a * 9; } else { r = a >> 1; } return r; }
// Unsigned comparisons, past the sign bit.
uPick x:u64 y:u64 -> u64 { r: u64 = 0; if (x < y) { r = y - x; } else { r = x + 1; } return r; }
// A condition fused with a load through an index, the arms reading values from before it.
countSplit xs:[long] lim:long -> long {
    lo: long = 0;
    for i in 0..xs.len {
        d: long = 0;
        if (xs[i] > lim) { d = 1000; } else { d = 1; }
        lo += d;
    }
    return lo;
}
// The one-armed shape: the best so far and where it was, a value of the arm's own, and a value
// the arm reads again after writing it.
argMax xs:[long] -> long {
    best: long = xs[0];
    at: long = 0;
    for i in 1..xs.len { v: long = xs[i]; if (v > best) { best = v; at = i; } }
    return at * 1000 + best;
}
armLocal a:long b:long -> long { r: long = b; if (a > 0) { t: long = a * 3; r = t + 1; } return r; }
reread a:long b:long -> long {
    x: long = 1;
    y: long = 2;
    if (a != b) { x = a; y = x + 5; }
    return x * 100 + y;
}
clamp x:long -> long { r: long = x; if (r > 100) { r = 100; } if (r < -100) { r = -100; } return r; }
// Many values live, so some arms read from slots and are written as branches.
crowd xs:[long] -> long {
    a: long = xs[0] * 3; b: long = xs[1] * 5; c: long = xs[2] * 7; d: long = xs[3] * 11;
    e: long = a + b; f: long = c + d; g: long = a - d; h: long = b - c;
    r: long = 0;
    for i in 0..xs.len {
        if (xs[i] > 2) { r = e + i; } else { r = g * 3; }
        if (xs[i] < 0) { r = r + h; }
    }
    return r + a + b + c + d + e + f + g + h;
}

main -> int {
    st: fn(long) -> long = &step;
    sts: fn(long) -> long = &steps;
    if (st(10) != 5 || st(7) != 22 || st(-4) != -2 || st(-3) != -8) { return 1; }
    if (sts(27) != 111 || sts(1) != 0 || sts(97) != 118) { return 2; }
    pk: fn(long, long, bool) -> long = &pick;
    pc: fn(long) -> long = &pickConst;
    pm: fn(long, long) -> long = &pickMixed;
    if (pk(4, 9, true) != 4 || pk(4, 9, false) != 9) { return 3; }
    if (pc(6) != 7 || pc(5) != -3 || pm(8, 1) != 8 || pm(8, 0) != 12) { return 4; }
    cc: fn(long, long, bool) -> long = &copyClash;
    if (cc(6, 3, true) != 510 || cc(6, 3, false) != 3309) { return 17; }
    bo: fn(long, long) -> long = &both;
    ei: fn(long, long) -> long = &either;
    if (bo(1, 1) != 2 || bo(1, -1) != 1 || bo(-1, 1) != 3) { return 18; }
    if (ei(1, -5) != 2 || ei(-1, 1) != 0 || ei(-1, -1) != 1) { return 19; }
    sp: fn(long, long, bool) -> long = &sumOrProd;
    wl: fn(long, long) -> long = &withLocal;
    if (sp(4, 5, true) != 9 || sp(4, 5, false) != 12 || wl(2, 3) != 13 || wl(3, 2) != -2) { return 5; }
    ma: fn(long, bool) -> long = &maskOrAdd;
    am: fn(long, bool) -> long = &addOrMask;
    xs: fn(long, long) -> long = &xorOrShift;
    if (ma(-1, true) != 15 || ma(-1, false) != 1 || am(-1, true) != 1 || am(-1, false) != 15) { return 6; }
    if (xs(6, 3) != 5 || xs(3, 6) != 24 || xs(-9, -9) != 0) { return 7; }
    nu: fn(u8, u8) -> u8 = &narrowU8;
    ni: fn(i16, i16) -> i16 = &narrowI16;
    nn: fn(int) -> int = &narrowInt;
    if (nu(100, 7) != 44 as u8 || nu(7, 100) != 44 as u8 || nu(0, 0) != 0 as u8) { return 8; }
    if (ni(-5000, 0) != 30536 as i16 || ni(5, -3) != -12 as i16 || ni(1, 10000) != -29999 as i16) { return 9; }
    if (nn(300000000) != -1594967296 || nn(-7) != -4 || nn(0) != 0) { return 10; }
    up: fn(u64, u64) -> u64 = &uPick;
    big: u64 = ~(0 as u64);
    if (up(3 as u64, big) != big - 3 as u64 || up(big, 3 as u64) != 0 as u64 || up(5 as u64, 5 as u64) != 6 as u64) { return 11; }
    data: [long; 8] = [5, -3, 0, 12, -7, 9, 2, 3];
    cs: fn([long], long) -> long = &countSplit;
    if (cs(data[..], 2) != 4004 || cs(data[..], 100) != 8) { return 12; }
    ax: fn([long]) -> long = &argMax;
    if (ax(data[..]) != 3012) { return 13; }
    al: fn(long, long) -> long = &armLocal;
    rr: fn(long, long) -> long = &reread;
    cl: fn(long) -> long = &clamp;
    if (al(4, 9) != 13 || al(-4, 9) != 9 || rr(7, 1) != 712 || rr(7, 7) != 102) { return 14; }
    if (cl(500) != 100 || cl(-500) != -100 || cl(42) != 42) { return 15; }
    cr: fn([long]) -> long = &crowd;
    if (cr(data[..]) != 139) { return 16; }
    return 0;
}
