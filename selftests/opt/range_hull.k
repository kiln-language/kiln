// Value ranges (`flow.k` `computeRanges`): `x & 7`, an unsigned `x % 8`, `k as long` of a u64 in
// [0, 7], a value that is 2 or 5 after a join, `x & m` with m in [0, 3], a signed remainder of a
// value never negative, `x >> 60` of a u64, and `i + 1` under `i < 8`: each an index whose
// check is gone. `x & 15` into 8 elements keeps it.
// ir-lacks: range_hull::mask bounds
// ir-lacks: range_hull::umod bounds
// ir-lacks: range_hull::join bounds
// ir-lacks: range_hull::both bounds
// ir-lacks: range_hull::smod bounds
// ir-lacks: range_hull::shift bounds
// ir-lacks: range_hull::next bounds
// ir-has: range_hull::wide bounds
var gX: long = 1234567;
var gU: u64 = 18446744073709551615;
var gB: bool = true;
mask x:long -> long { a: [long; 8]; for i in 0..8 { a[i] = i * 10; } return a[x & 7]; }
umod x:u64 -> long { a: [long; 8]; for i in 0..8 { a[i] = i * 10; } k: u64 = x % 8; return a[k as long]; }
join b:bool -> long {
    a: [long; 8];
    for i in 0..8 { a[i] = i * 10; }
    k: long = 2;
    if (b) { k = 5; }
    return a[k];
}
both x:long y:long -> long { a: [long; 8]; for i in 0..8 { a[i] = i; } m: long = y & 3; return a[x & m]; }
smod x:long -> long { a: [long; 8]; for i in 0..8 { a[i] = i; } if (x < 0) { return -1; } return a[x % 8]; }
shift x:u64 -> long { a: [long; 16]; for i in 0..16 { a[i] = i; } return a[(x >> 60) as long]; }
next n:long -> long {
    a: [long; 9];
    for i in 0..9 { a[i] = i; }
    s: long = 0;
    i: long = 0;
    while (i < 8) { j: long = i + 1; s = s + a[j]; i = i + 1; }
    return s;
}
wide x:long -> long { a: [long; 8]; for i in 0..8 { a[i] = i; } return a[x & 15]; }
main -> int {
    if (mask(gX) != 70 || umod(gU) != 70 || join(gB) != 50 || join(!gB) != 20) { return 1; }
    if (both(gX, -1) != 3 || smod(gX) != 7 || smod(0 - gX) != -1 || shift(gU) != 15) { return 2; }
    if (next(gX) != 36 || wide(gX & 7) != 7) { return 3; }
    return 0;
}
