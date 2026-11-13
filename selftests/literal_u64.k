// Integer literals up to 2^64 - 1, with `_` between digits: past `long`'s maximum a literal is a
// u64's and goes where a u64 goes; `long`'s minimum is still a long. 1 + 2 + 4 + 8 + 16 + 32 = 63.
takeU x:u64 -> u64 { return x; }
main -> int {
    t: long = 0;
    a: u64 = 18446744073709551615;
    b: u64 = 0xFFFF_FFFF_FFFF_FFFF;
    c: u64 = 9_223_372_036_854_775_808;
    m: long = -9223372036854775808;
    if (a == b) { t = t + 1; }
    if (c == (1 as u64) << (63 as u64)) { t = t + 2; }
    if (m < 0 && m - 1 > 0) { t = t + 4; }               // wraps to the maximum
    if (takeU(0x8000_0000_0000_0000) == c) { t = t + 8; }
    if (1_000_000 == 1000000) { t = t + 16; }
    if (a > c) { t = t + 32; }
    return t as int;
}
