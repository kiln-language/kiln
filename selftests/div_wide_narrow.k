// A division by a value: when both operands' high halves are zero the 32-bit `div` does it, and
// otherwise the 64-bit divide out of line. Operands either side of 2^32 and of zero, every width,
// the narrow signed wrap (`int` -2^31 / -1 is -2^31, and must not fault), divisors in registers
// and in slots, and a counted loop of remainders. Through fn values, so nothing folds.

q x:long y:long -> long { return x / y; }
r x:long y:long -> long { return x % y; }
qi x:int y:int -> int { return x / y; }
ri x:int y:int -> int { return x % y; }
qs x:i16 y:i16 -> i16 { return x / y; }
qu x:u32 y:u32 -> u32 { return x / y; }
ru x:u32 y:u32 -> u32 { return x % y; }
qb x:u8 y:u8 -> u8 { return x / y; }
qw x:u64 y:u64 -> u64 { return x / y; }
rw x:u64 y:u64 -> u64 { return x % y; }
// Divisors kept in slots: many values live at once.
crowd x:long a:long b:long c:long d:long -> long {
    p: long = x / a; s: long = x % b; t: long = x / c; u: long = x % d;
    v: long = (x + 1) / a; w: long = (x + 2) % b; y: long = (x + 3) / c; z: long = (x + 4) % d;
    return p + 2 * s + 3 * t + 4 * u + 5 * v + 6 * w + 7 * y + 8 * z;
}
primes n:long -> long {
    c: long = 0;
    for k in 2..n {
        i: long = 2;
        prime: bool = true;
        while (i * i <= k) { if (k % i == 0) { prime = false; break; } i += 1; }
        if (prime) { c += 1; }
    }
    return c;
}

main -> int {
    a: fn(long, long) -> long = &q;
    b: fn(long, long) -> long = &r;
    if (a(100, 7) != 14 || a(4294967295, 2) != 2147483647 || a(4294967296, 2) != 2147483648) { return 1; }
    if (a(-100, 7) != -14 || a(100, -7) != -14 || a(-100, -7) != 14) { return 2; }
    if (a(9223372036854775807, 4294967296) != 2147483647 || a(5, 4294967296) != 0) { return 3; }
    if (b(100, 7) != 2 || b(-100, 7) != -2 || b(100, -7) != 2 || b(4294967297, 4294967296) != 1) { return 4; }
    if (b(0 - 9223372036854775807 - 1, 3) != -2 || a(0 - 9223372036854775807 - 1, 2) != 0 - 4611686018427387904) { return 5; }
    c: fn(int, int) -> int = &qi;
    d: fn(int, int) -> int = &ri;
    lo: int = 0 - 2147483647 - 1;
    if (c(lo, -1) != lo || d(lo, -1) != 0 || c(-7, 2) != -3 || d(-7, 2) != -1 || c(2147483647, 2) != 1073741823) { return 6; }
    e: fn(i16, i16) -> i16 = &qs;
    if (e(-32768 as i16, -1 as i16) != -32768 as i16 || e(-9 as i16, 4 as i16) != -2 as i16) { return 7; }
    f: fn(u32, u32) -> u32 = &qu;
    g: fn(u32, u32) -> u32 = &ru;
    if (f(4294967295, 2) != 2147483647 || g(4294967295, 4294967294) != 1 || f(7, 4294967295) != 0) { return 8; }
    h: fn(u8, u8) -> u8 = &qb;
    if (h(255, 2) != 127 || h(1, 255) != 0) { return 9; }
    k: fn(u64, u64) -> u64 = &qw;
    m: fn(u64, u64) -> u64 = &rw;
    top: u64 = ~(0 as u64);
    if (k(top, 2 as u64) != 9223372036854775807 as u64 || m(top, 4294967296) != 4294967295 as u64 || k(10 as u64, 3 as u64) != 3 as u64) { return 10; }
    cr: fn(long, long, long, long, long) -> long = &crowd;
    if (cr(1000, 3, 7, 11, 13) != 333 + 2 * 6 + 3 * 90 + 4 * 12 + 5 * 333 + 6 * 1 + 7 * 91 + 8 * 3) { return 11; }
    if (cr(-1000, 3, 7, 11, 13) != -333 - 2 * 6 - 3 * 90 - 4 * 12 - 5 * 333 - 6 * 4 - 7 * 90 - 8 * 8) { return 12; }
    pr: fn(long) -> long = &primes;
    if (pr(100) != 25 || pr(2) != 0) { return 13; }
    return 0;
}
