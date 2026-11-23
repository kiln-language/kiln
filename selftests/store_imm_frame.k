// A constant stored is the store's immediate (its low bytes, at every width; at eight bytes only
// one the sign-extended 32-bit field holds), and a frame slot's address is part of the addressing
// mode (`[rbp + rcx*4 - 400]`), with an index, a field offset, or neither. Through fn values,
// so nothing folds the stores away.

struct Mixed { a: u8, b: i16, c: int, d: long, e: u32 }

fillBytes n:long -> long {
    xs: [u8; 64];
    for i in 0..n { xs[i] = 200; }
    xs[n] = 255;
    xs[n + 1] = (300 - 256) as u8;
    s: long = 0;
    for i in 0..n + 2 { s += xs[i] as long; }
    return s;
}
fillChars n:long -> long {
    xs: [char; 64];
    m: long = -128;
    for i in 0..n { xs[i] = m as char; }
    s: long = 0;
    for i in 0..n { s += xs[i] as long; }
    return s;
}
fillShorts n:long -> long {
    xs: [i16; 64];
    for i in 0..n { xs[i] = -32768 as i16; }
    s: long = 0;
    for i in 0..n { s += xs[i] as long; }
    return s;
}
fillInts n:long -> long {
    xs: [int; 100];
    for i in 0..n { xs[i] = -1; }
    for i in 0..n { if (i % 3 == 0) { xs[i] = 2147483647; } }
    s: long = 0;
    for i in 0..n { s += xs[i] as long; }
    return s;
}
fillU32 n:long -> long {
    xs: [u32; 40];
    for i in 0..n { xs[i] = 4294967295; }
    s: long = 0;
    for i in 0..n { s += xs[i] as long; }
    return s;
}
// Eight bytes: one constant fits the immediate, one does not, one is the most negative that does.
fillLongs n:long -> long {
    xs: [long; 40];
    for i in 0..n { xs[i] = -7; }
    for i in 0..n { if (i % 2 == 0) { xs[i] = 81985529216486895; } }
    xs[0] = 0 - 2147483648;
    s: long = 0;
    for i in 0..n { s += xs[i]; }
    return s;
}
fillU64 n:long -> u64 {
    xs: [u64; 8];
    for i in 0..n { xs[i] = ~(0 as u64); }
    s: u64 = 0 as u64;
    for i in 0..n { s = s + (xs[i] >> (60 as u64)); }
    return s;
}
fields k:long -> long {
    m: Mixed = Mixed { a: 0, b: 0, c: 0, d: 0, e: 0 };
    m.a = 250;
    m.b = -2 as i16;
    m.c = -3;
    m.d = 1 << 40;
    m.e = 4000000000;
    if (k > 0) { m.d = -1; }
    return m.a as long + m.b as long + m.c as long + m.d + m.e as long;
}
// Two arrays live at once, read and written through their own slots.
twoArrays n:long -> long {
    a: [long; 32];
    b: [int; 32];
    for i in 0..n { a[i] = i * 3; b[i] = 5; }
    s: long = 0;
    for i in 0..n { s += a[i] * b[i] as long; }
    return s;
}

main -> int {
    fb: fn(long) -> long = &fillBytes;
    fc: fn(long) -> long = &fillChars;
    fs: fn(long) -> long = &fillShorts;
    fi: fn(long) -> long = &fillInts;
    fu: fn(long) -> long = &fillU32;
    fl: fn(long) -> long = &fillLongs;
    fw: fn(long) -> u64 = &fillU64;
    ff: fn(long) -> long = &fields;
    ta: fn(long) -> long = &twoArrays;
    if (fb(10) != 2000 + 255 + 44 || fb(0) != 299) { return 1; }
    if (fc(5) != -640) { return 2; }
    if (fs(3) != -98304) { return 3; }
    if (fi(10) != 4 * 2147483647 - 6) { return 4; }
    if (fu(3) != 3 * 4294967295) { return 5; }
    if (fl(4) != 0 - 2147483648 + 81985529216486895 - 14) { return 6; }
    if (fw(5) != 75 as u64) { return 7; }
    if (ff(0) != 250 - 2 - 3 + (1 << 40) + 4000000000 || ff(1) != 250 - 2 - 3 - 1 + 4000000000) { return 8; }
    if (ta(10) != 675) { return 9; }
    return 0;
}
