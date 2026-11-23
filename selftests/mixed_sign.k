// Four bytes and wider: two integers neither of which holds the other meet at the narrowest signed
// type that holds both (`u32 + int` is a `long`, so a comparison orders by value); a literal takes
// the other operand's type when its value is one of that type's; a shift is its left operand's
// type. Checked three ways: at run time on values the optimizer cannot see, with constants it
// folds, and in the evaluator (a global's initializer running the same checks).

var gV: long = 0;
dyn v:long -> long { gV = v; return gV; }

checkMeet p:long q:long -> long {
    u: u32 = p as u32;
    i: int = q as int;
    c: char = q as char;
    s: u16 = p as u16;
    ul: long = u as long;
    il: long = i as long;
    cl: long = c as long;
    sl: long = s as long;
    bad: long = 0;
    if ((u < i) != (ul < il)) { bad = bad + 1; }          // by value: 4000000000 is not below -1
    if ((i < u) != (il < ul)) { bad = bad + 1; }
    if ((u == i) != (ul == il)) { bad = bad + 1; }
    if ((u >= i) != (ul >= il)) { bad = bad + 1; }
    r1: long = u + i;                                     // a long: no wrap at 32 bits
    if (r1 != ul + il) { bad = bad + 1; }
    r2: long = i - u;
    if (r2 != il - ul) { bad = bad + 1; }
    r3: long = u * c;                                     // u32 and char: a long
    if (r3 != ul * cl) { bad = bad + 1; }
    r4: int = s + i;                                      // a u16 widens into an int
    if ((r4 as long) != ((sl + il) as int) as long) { bad = bad + 1; }
    if ((u < c) != (ul < cl)) { bad = bad + 1; }
    if (u / 7 != (ul / 7) as u32) { bad = bad + 1; }       // the literal is a u32: unsigned
    return bad;
}

checkLiterals p:long q:long -> long {
    u: u32 = p as u32;
    h: u64 = q as u64;
    b: u8 = p as u8;
    ul: long = u as long;
    bad: long = 0;
    if (u < 0) { bad = bad + 1; }                          // a u32 against 0: never below
    if ((u + 1) as long != ((ul + 1) as u32) as long) { bad = bad + 1; }   // a u32 sum wraps
    if ((u > 3000000000) != (ul > 3000000000)) { bad = bad + 1; }
    if ((u > 5000000000) != false) { bad = bad + 1; }    // no u32: a long, compared by value
    g: u64 = h * 31 + 7;                                   // a u64 throughout
    if (g != (((q * 31) + 7) as u64)) { bad = bad + 1; }
    if ((h >> 60) != ((q as u64) >> 60)) { bad = bad + 1; }
    if ((b + 1) as long != (((p as u8) as long + 1) as u8) as long) { bad = bad + 1; }
    return bad;
}

checkShifts p:long q:long -> long {
    b: u8 = p as u8;
    k: long = (q & 7) + 1;
    ki: int = k as int;
    h: u64 = p as u64;
    i: int = q as int;
    bad: long = 0;
    if ((b << k) as long != (((b as long) << k) & 255)) { bad = bad + 1; }   // a u8: wraps at 8
    if ((h >> k) != (h >> (k as u64))) { bad = bad + 1; }                 // a u64 by a long
    if ((i << ki) as long != (((i as long) << k) as int) as long) { bad = bad + 1; }
    w: long = 1 << (k + 40);                               // a literal takes a long count's type
    if (w != (1 as long) << (k + 40)) { bad = bad + 1; }
    m: long = 1 << (ki + 40);                              // and a long destination's
    if (m != (1 as long) << (k + 40)) { bad = bad + 1; }
    return bad;
}

VALUES: [long; 12] = [0, 1, -1, 7, 255, 65535, 2147483647, -2147483648, 4000000000, 4294967295, -4000000000, 1234567891234];

all lo:long hi:long -> long {
    bad: long = 0;
    for i in lo..hi {
        for j in lo..hi {
            if (checkMeet(VALUES[i], VALUES[j]) != 0) { bad = bad | 1; }
            if (checkLiterals(VALUES[i], VALUES[j]) != 0) { bad = bad | 2; }
            if (checkShifts(VALUES[i], VALUES[j]) != 0) { bad = bad | 4; }
        }
    }
    return bad;
}

AT_COMPILE: long = all(0, 12);

main -> int {
    bad: long = 0;
    for i in 0..12 {
        for j in 0..12 {
            p: long = dyn(VALUES[i]);
            q: long = dyn(VALUES[j]);
            if (checkMeet(p, q) != 0) { bad = bad | 1; }
            if (checkLiterals(p, q) != 0) { bad = bad | 2; }
            if (checkShifts(p, q) != 0) { bad = bad | 4; }
        }
    }
    if (checkMeet(4000000000, -1) != 0 || checkLiterals(4294967295, -1) != 0 || checkShifts(255, 7) != 0) { bad = bad | 8; }
    if (AT_COMPILE != 0) { bad = bad | 16; }
    return bad as int;
}
