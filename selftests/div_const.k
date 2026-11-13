// A division or remainder by a constant is a multiply by its reciprocal (or shifts, for a power
// of two), and it must give exactly what `idiv`/`div` gives for every dividend: zero, one, minus
// one, both ends of the range, either side of every power of two, and a long run of pseudo-random
// values of every magnitude, at every integer width, signed and unsigned. The reference is the
// same division by a value the optimizer cannot see (a `var` global read back), which stays a
// hardware division. Exit 0 when all agree; otherwise which width disagreed first.
var gDiv: long = 0;
dyn v:long -> long { gDiv = v; return gDiv; }

checkLong x:long -> long {
    bad: long = 0;
    if (x / 2 != x / dyn(2) || x % 2 != x % dyn(2)) { bad = bad + 1; }
    if (x / 3 != x / dyn(3) || x % 3 != x % dyn(3)) { bad = bad + 1; }
    if (x / 4 != x / dyn(4) || x % 4 != x % dyn(4)) { bad = bad + 1; }
    if (x / 5 != x / dyn(5) || x % 5 != x % dyn(5)) { bad = bad + 1; }
    if (x / 6 != x / dyn(6) || x % 6 != x % dyn(6)) { bad = bad + 1; }
    if (x / 7 != x / dyn(7) || x % 7 != x % dyn(7)) { bad = bad + 1; }
    if (x / 10 != x / dyn(10) || x % 10 != x % dyn(10)) { bad = bad + 1; }
    if (x / 11 != x / dyn(11) || x % 11 != x % dyn(11)) { bad = bad + 1; }
    if (x / 25 != x / dyn(25) || x % 25 != x % dyn(25)) { bad = bad + 1; }
    if (x / 641 != x / dyn(641) || x % 641 != x % dyn(641)) { bad = bad + 1; }
    if (x / 1000 != x / dyn(1000) || x % 1000 != x % dyn(1000)) { bad = bad + 1; }
    if (x / 1024 != x / dyn(1024) || x % 1024 != x % dyn(1024)) { bad = bad + 1; }
    if (x / 65537 != x / dyn(65537) || x % 65537 != x % dyn(65537)) { bad = bad + 1; }
    if (x / 1000000007 != x / dyn(1000000007) || x % 1000000007 != x % dyn(1000000007)) { bad = bad + 1; }
    if (x / 1073741824 != x / dyn(1073741824) || x % 1073741824 != x % dyn(1073741824)) { bad = bad + 1; }
    if (x / 2147483647 != x / dyn(2147483647) || x % 2147483647 != x % dyn(2147483647)) { bad = bad + 1; }
    return bad;
}

checkU64 x:u64 -> long {
    bad: long = 0;
    if (x / (2 as u64) != x / (dyn(2) as u64) || x % (2 as u64) != x % (dyn(2) as u64)) { bad = bad + 1; }
    if (x / (3 as u64) != x / (dyn(3) as u64) || x % (3 as u64) != x % (dyn(3) as u64)) { bad = bad + 1; }
    if (x / (7 as u64) != x / (dyn(7) as u64) || x % (7 as u64) != x % (dyn(7) as u64)) { bad = bad + 1; }
    if (x / (10 as u64) != x / (dyn(10) as u64) || x % (10 as u64) != x % (dyn(10) as u64)) { bad = bad + 1; }
    if (x / (641 as u64) != x / (dyn(641) as u64) || x % (641 as u64) != x % (dyn(641) as u64)) { bad = bad + 1; }
    if (x / (1000 as u64) != x / (dyn(1000) as u64) || x % (1000 as u64) != x % (dyn(1000) as u64)) { bad = bad + 1; }
    if (x / (4096 as u64) != x / (dyn(4096) as u64) || x % (4096 as u64) != x % (dyn(4096) as u64)) { bad = bad + 1; }
    if (x / (1000000007 as u64) != x / (dyn(1000000007) as u64) || x % (1000000007 as u64) != x % (dyn(1000000007) as u64)) { bad = bad + 1; }
    if (x / (2147483647 as u64) != x / (dyn(2147483647) as u64) || x % (2147483647 as u64) != x % (dyn(2147483647) as u64)) { bad = bad + 1; }
    return bad;
}

checkInt x:int -> long {
    bad: long = 0;
    if (x / 3 != x / (dyn(3) as int) || x % 3 != x % (dyn(3) as int)) { bad = bad + 1; }
    if (x / 7 != x / (dyn(7) as int) || x % 7 != x % (dyn(7) as int)) { bad = bad + 1; }
    if (x / 8 != x / (dyn(8) as int) || x % 8 != x % (dyn(8) as int)) { bad = bad + 1; }
    if (x / 100 != x / (dyn(100) as int) || x % 100 != x % (dyn(100) as int)) { bad = bad + 1; }
    if (x / 2147483647 != x / (dyn(2147483647) as int) || x % 2147483647 != x % (dyn(2147483647) as int)) { bad = bad + 1; }
    return bad;
}

checkU32 x:u32 -> long {
    bad: long = 0;
    if (x / (3 as u32) != x / (dyn(3) as u32) || x % (3 as u32) != x % (dyn(3) as u32)) { bad = bad + 1; }
    if (x / (7 as u32) != x / (dyn(7) as u32) || x % (7 as u32) != x % (dyn(7) as u32)) { bad = bad + 1; }
    if (x / (10 as u32) != x / (dyn(10) as u32) || x % (10 as u32) != x % (dyn(10) as u32)) { bad = bad + 1; }
    if (x / (16 as u32) != x / (dyn(16) as u32) || x % (16 as u32) != x % (dyn(16) as u32)) { bad = bad + 1; }
    return bad;
}

checkNarrow x:i16 y:u8 c:char -> long {
    bad: long = 0;
    if (x / (3 as i16) != x / (dyn(3) as i16) || x % (3 as i16) != x % (dyn(3) as i16)) { bad = bad + 1; }
    if (x / (128 as i16) != x / (dyn(128) as i16) || x % (128 as i16) != x % (dyn(128) as i16)) { bad = bad + 1; }
    if (y / (3 as u8) != y / (dyn(3) as u8) || y % (3 as u8) != y % (dyn(3) as u8)) { bad = bad + 1; }
    if (y / (10 as u8) != y / (dyn(10) as u8) || y % (10 as u8) != y % (dyn(10) as u8)) { bad = bad + 1; }
    if (c / (7 as char) != c / (dyn(7) as char) || c % (7 as char) != c % (dyn(7) as char)) { bad = bad + 1; }
    return bad;
}

one x:long -> long {
    bad: long = 0;
    if (checkLong(x) != 0) { bad = bad | 1; }
    if (checkU64(x as u64) != 0) { bad = bad | 2; }
    if (checkInt(x as int) != 0) { bad = bad | 4; }
    if (checkU32(x as u32) != 0) { bad = bad | 8; }
    if (checkNarrow(x as i16, x as u8, x as char) != 0) { bad = bad | 16; }
    return bad;
}

main -> int {
    bad: long = 0;
    max: long = 9223372036854775807;
    min: long = 0 - max - 1;
    edges: [long; 24] = [0, 1, 2, 3, 6, 7, 8, 999, 1000, 1001, 2147483647, 2147483648, 4294967295,
                         4294967296, 4611686018427387904, max, max - 1, max - 6, -1, -7, -1000, min,
                         min + 1, -2147483648];
    for i in 0..24 {
        bad = bad | one(edges[i]);
        bad = bad | one(0 - edges[i]);
        bad = bad | one(edges[i] + 1);
        bad = bad | one(edges[i] - 1);
    }
    // Every magnitude: xorshift, then shifted down by every amount.
    s: u64 = 88172645463325252 as u64;
    for k in 0..3000 {
        s = s ^ (s << (13 as u64));
        s = s ^ (s >> (7 as u64));
        s = s ^ (s << (17 as u64));
        v: long = (s >> ((k % 64) as u64)) as long;
        bad = bad | one(v);
        bad = bad | one(0 - v);
    }
    return bad as int;
}
