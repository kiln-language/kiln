// Arithmetic on an integer type is computed at that type and wraps at its width, two's
// complement, at every width and signedness: `u8 + u8` is a `u8` (200 + 100 is 44), as `int + int`
// has always wrapped at thirty-two bits. A value stored into a narrower variable, field or element
// is narrowed to it. The oracle for each operation is the same operation on `long`s, converted
// with `as` (which has always been the canonical form). Each check runs three ways: at run time
// on values the optimizer cannot see (a `var` global read back), with constants the optimizer
// folds, and at compile time (an immutable global's initializer, run by the evaluator); all
// three must agree. Exit 0 when they do; otherwise a bit per width that disagreed.
var gV: long = 0;
dyn v:long -> long { gV = v; return gV; }

struct Cells { a: u8, b: char, c: u16, d: i16, e: u32, f: int }

// ─── u8 ──────────────────────────────────────────────────────────────────────
addU8 a:u8 b:u8 -> u8 { return a + b; }
subU8 a:u8 b:u8 -> u8 { return a - b; }
mulU8 a:u8 b:u8 -> u8 { return a * b; }
shlU8 a:u8 k:u8 -> u8 { return a << k; }
shrU8 a:u8 k:u8 -> u8 { return a >> k; }
notU8 a:u8 -> u8 { return ~a; }
checkU8 p:long q:long -> long {
    x: u8 = p as u8;
    y: u8 = q as u8;
    xl: long = x as long;
    yl: long = y as long;
    k: u8 = (q & 7) as u8;
    kl: long = k as long;
    bad: long = 0;
    if (addU8(x, y) != (xl + yl) as u8) { bad = bad + 1; }
    if (subU8(x, y) != (xl - yl) as u8) { bad = bad + 1; }
    if (mulU8(x, y) != (xl * yl) as u8) { bad = bad + 1; }
    if (shlU8(x, k) != (xl << kl) as u8) { bad = bad + 1; }
    if (shrU8(x, k) != (xl >> kl) as u8) { bad = bad + 1; }
    if (notU8(x) != (~xl) as u8) { bad = bad + 1; }
    if (y != (0 as u8) && x / y != (xl / yl) as u8) { bad = bad + 1; }
    w: long = x + y;                            // the wrapped value, widened
    if (w != ((xl + yl) as u8) as long) { bad = bad + 1; }
    n: u8 = -x;                                 // an int, narrowed by the store
    if (n != (0 - xl) as u8) { bad = bad + 1; }
    z: u8 = x;
    z += y;   if (z != (xl + yl) as u8) { bad = bad + 1; }
    z = x;
    z -= y;   if (z != (xl - yl) as u8) { bad = bad + 1; }
    z = x;
    z *= y;   if (z != (xl * yl) as u8) { bad = bad + 1; }
    z = x;
    z <<= 3;  if (z != (xl << 3) as u8) { bad = bad + 1; }
    c: Cells = Cells { a: x, b: 0, c: 0, d: 0, e: 0, f: 0 };
    c.a += y; if (c.a != (xl + yl) as u8) { bad = bad + 1; }
    c.a = x * y; if (c.a != (xl * yl) as u8) { bad = bad + 1; }
    arr: [u8; 3] = [x, y, x];
    arr[1] += x; if (arr[1] != (yl + xl) as u8) { bad = bad + 1; }
    arr[2] = arr[0] * arr[1]; if (arr[2] != (xl * ((yl + xl) as u8) as long) as u8) { bad = bad + 1; }
    return bad;
}

// ─── char (i8) ───────────────────────────────────────────────────────────────
addI8 a:char b:char -> char { return a + b; }
subI8 a:char b:char -> char { return a - b; }
mulI8 a:char b:char -> char { return a * b; }
shlI8 a:char k:char -> char { return a << k; }
shrI8 a:char k:char -> char { return a >> k; }
divI8 a:char b:char -> char { return a / b; }
checkI8 p:long q:long -> long {
    x: char = p as char;
    y: char = q as char;
    xl: long = x as long;
    yl: long = y as long;
    k: char = (q & 7) as char;
    kl: long = k as long;
    bad: long = 0;
    if (addI8(x, y) != (xl + yl) as char) { bad = bad + 1; }
    if (subI8(x, y) != (xl - yl) as char) { bad = bad + 1; }
    if (mulI8(x, y) != (xl * yl) as char) { bad = bad + 1; }
    if (shlI8(x, k) != (xl << kl) as char) { bad = bad + 1; }
    if (shrI8(x, k) != (xl >> kl) as char) { bad = bad + 1; }
    if (y != (0 as char) && divI8(x, y) != (xl / yl) as char) { bad = bad + 1; }   // -128 / -1 is -128
    if (y != (0 as char) && x % y != (xl % yl) as char) { bad = bad + 1; }
    w: long = x * y;
    if (w != ((xl * yl) as char) as long) { bad = bad + 1; }
    n: char = -x;
    if (n != (0 - xl) as char) { bad = bad + 1; }
    z: char = x;
    z += y;   if (z != (xl + yl) as char) { bad = bad + 1; }
    z = x;
    z *= y;   if (z != (xl * yl) as char) { bad = bad + 1; }
    c: Cells = Cells { a: 0, b: x, c: 0, d: 0, e: 0, f: 0 };
    c.b -= y; if (c.b != (xl - yl) as char) { bad = bad + 1; }
    arr: [char; 2] = [x, y];
    arr[0] *= y; if (arr[0] != (xl * yl) as char) { bad = bad + 1; }
    return bad;
}

// ─── u16 ─────────────────────────────────────────────────────────────────────
addU16 a:u16 b:u16 -> u16 { return a + b; }
subU16 a:u16 b:u16 -> u16 { return a - b; }
mulU16 a:u16 b:u16 -> u16 { return a * b; }
shlU16 a:u16 k:u16 -> u16 { return a << k; }
checkU16 p:long q:long -> long {
    x: u16 = p as u16;
    y: u16 = q as u16;
    xl: long = x as long;
    yl: long = y as long;
    k: u16 = (q & 15) as u16;
    kl: long = k as long;
    bad: long = 0;
    if (addU16(x, y) != (xl + yl) as u16) { bad = bad + 1; }
    if (subU16(x, y) != (xl - yl) as u16) { bad = bad + 1; }
    if (mulU16(x, y) != (xl * yl) as u16) { bad = bad + 1; }
    if (shlU16(x, k) != (xl << kl) as u16) { bad = bad + 1; }
    if ((x >> k) != (xl >> kl) as u16) { bad = bad + 1; }
    if (~x != (~xl) as u16) { bad = bad + 1; }
    w: long = x * y;
    if (w != ((xl * yl) as u16) as long) { bad = bad + 1; }
    n: u16 = -x;
    if (n != (0 - xl) as u16) { bad = bad + 1; }
    z: u16 = x;
    z -= y;   if (z != (xl - yl) as u16) { bad = bad + 1; }
    c: Cells = Cells { a: 0, b: 0, c: x, d: 0, e: 0, f: 0 };
    c.c *= y; if (c.c != (xl * yl) as u16) { bad = bad + 1; }
    arr: [u16; 2] = [x, y];
    arr[1] += x; if (arr[1] != (yl + xl) as u16) { bad = bad + 1; }
    return bad;
}

// ─── i16 ─────────────────────────────────────────────────────────────────────
addI16 a:i16 b:i16 -> i16 { return a + b; }
subI16 a:i16 b:i16 -> i16 { return a - b; }
mulI16 a:i16 b:i16 -> i16 { return a * b; }
shlI16 a:i16 k:i16 -> i16 { return a << k; }
checkI16 p:long q:long -> long {
    x: i16 = p as i16;
    y: i16 = q as i16;
    xl: long = x as long;
    yl: long = y as long;
    k: i16 = (q & 15) as i16;
    kl: long = k as long;
    bad: long = 0;
    if (addI16(x, y) != (xl + yl) as i16) { bad = bad + 1; }
    if (subI16(x, y) != (xl - yl) as i16) { bad = bad + 1; }
    if (mulI16(x, y) != (xl * yl) as i16) { bad = bad + 1; }
    if (shlI16(x, k) != (xl << kl) as i16) { bad = bad + 1; }
    if ((x >> k) != (xl >> kl) as i16) { bad = bad + 1; }
    if (y != (0 as i16) && x / y != (xl / yl) as i16) { bad = bad + 1; }
    w: long = x + y;
    if (w != ((xl + yl) as i16) as long) { bad = bad + 1; }
    n: i16 = -x;
    if (n != (0 - xl) as i16) { bad = bad + 1; }
    z: i16 = x;
    z *= y;   if (z != (xl * yl) as i16) { bad = bad + 1; }
    c: Cells = Cells { a: 0, b: 0, c: 0, d: x, e: 0, f: 0 };
    c.d += y; if (c.d != (xl + yl) as i16) { bad = bad + 1; }
    arr: [i16; 2] = [x, y];
    arr[0] -= y; if (arr[0] != (xl - yl) as i16) { bad = bad + 1; }
    return bad;
}

// ─── u32 and int (these always wrapped; held to it) ──────────────────────────
addU32 a:u32 b:u32 -> u32 { return a + b; }
mulU32 a:u32 b:u32 -> u32 { return a * b; }
addI32 a:int b:int -> int { return a + b; }
mulI32 a:int b:int -> int { return a * b; }
checkW32 p:long q:long -> long {
    x: u32 = p as u32;
    y: u32 = q as u32;
    xl: long = x as long;
    yl: long = y as long;
    i: int = p as int;
    j: int = q as int;
    il: long = i as long;
    jl: long = j as long;
    bad: long = 0;
    if (addU32(x, y) != (xl + yl) as u32) { bad = bad + 1; }
    if (mulU32(x, y) != (xl * yl) as u32) { bad = bad + 1; }
    if ((x << 7) != (xl << 7) as u32) { bad = bad + 1; }
    if (addI32(i, j) != (il + jl) as int) { bad = bad + 1; }
    if (mulI32(i, j) != (il * jl) as int) { bad = bad + 1; }
    u: u32 = i as u32;                          // same width, other signedness: narrowed
    if ((u as long) != (il & 4294967295)) { bad = bad + 1; }
    c: Cells = Cells { a: 0, b: 0, c: 0, d: 0, e: x, f: i };
    c.e += y; if (c.e != (xl + yl) as u32) { bad = bad + 1; }
    c.f *= j; if (c.f != (il * jl) as int) { bad = bad + 1; }
    return bad;
}

// ─── operands of two narrow types meet at what holds both ───────────────────
checkMixed p:long q:long -> long {
    a: u8 = p as u8;
    c: char = q as char;
    s: u16 = q as u16;
    t: i16 = p as i16;
    al: long = a as long;
    cl: long = c as long;
    sl: long = s as long;
    tl: long = t as long;
    bad: long = 0;
    r1: long = a + c;                           // i16: neither holds the other
    if (r1 != al + cl) { bad = bad + 1; }
    if ((a < c) != (al < cl)) { bad = bad + 1; }   // ordered by value, not as unsigned
    r2: long = a + s;                           // u16: a u8 widens into it
    if (r2 != ((al + sl) as u16) as long) { bad = bad + 1; }
    r3: long = s + t;                           // int
    if (r3 != sl + tl) { bad = bad + 1; }
    r4: long = c * s;                           // int
    if (r4 != cl * sl) { bad = bad + 1; }
    zero: char = '0';
    r5: long = a - zero;                        // a u8 minus a char: i16
    if (r5 != al - 48) { bad = bad + 1; }
    r6: long = a - '0';                         // a literal takes the u8's type: a u8, wrapped
    if (r6 != ((al - 48) as u8) as long) { bad = bad + 1; }
    r7: long = a + 1;                           // so does `1`
    if (r7 != ((al + 1) as u8) as long) { bad = bad + 1; }
    r8: long = a + 300;                         // 300 is no u8: an int, the value
    if (r8 != al + 300) { bad = bad + 1; }
    return bad;
}

VALUES: [long; 16] = [0, 1, -1, 2, 127, 128, 255, 256, -128, -129, 32767, 32768, 65535, 2147483647, -2147483648, 1234567891];

all lo:long hi:long -> long {
    bad: long = 0;
    for i in lo..hi {
        for j in lo..hi {
            p: long = VALUES[i];
            q: long = VALUES[j];
            if (checkU8(p, q) != 0) { bad = bad | 1; }
            if (checkI8(p, q) != 0) { bad = bad | 2; }
            if (checkU16(p, q) != 0) { bad = bad | 4; }
            if (checkI16(p, q) != 0) { bad = bad | 8; }
            if (checkW32(p, q) != 0) { bad = bad | 16; }
            if (checkMixed(p, q) != 0) { bad = bad | 32; }
        }
    }
    return bad;
}

// Computed by the evaluator while compiling.
AT_COMPILE: long = all(0, 16);
ADD_U8: u8 = addU8(200, 100);
MUL_I8: char = mulI8(100, 3);
SUB_U16: u16 = subU16(1, 2);

main -> int {
    bad: long = 0;
    // At run time, on values the optimizer cannot see.
    for i in 0..16 {
        for j in 0..16 {
            p: long = dyn(VALUES[i]);
            q: long = dyn(VALUES[j]);
            if (checkU8(p, q) != 0) { bad = bad | 1; }
            if (checkI8(p, q) != 0) { bad = bad | 2; }
            if (checkU16(p, q) != 0) { bad = bad | 4; }
            if (checkI16(p, q) != 0) { bad = bad | 8; }
            if (checkW32(p, q) != 0) { bad = bad | 16; }
            if (checkMixed(p, q) != 0) { bad = bad | 32; }
        }
    }
    // Constants the optimizer folds, and the evaluator's answers.
    if (checkU8(200, 100) != 0 || checkI8(100, 3) != 0 || checkU16(65535, 2) != 0
        || checkI16(32767, 1) != 0 || checkW32(2147483647, 3) != 0 || checkMixed(200, -1) != 0) { bad = bad | 64; }
    if (AT_COMPILE != 0) { bad = bad | 128; }
    if (ADD_U8 != addU8(dyn(200) as u8, dyn(100) as u8) || ADD_U8 != (44 as u8)) { bad = bad | 64; }
    if (MUL_I8 != mulI8(dyn(100) as char, dyn(3) as char) || MUL_I8 != (44 as char)) { bad = bad | 64; }
    if (SUB_U16 != subU16(dyn(1) as u16, dyn(2) as u16) || SUB_U16 != (65535 as u16)) { bad = bad | 64; }
    return bad as int;
}
