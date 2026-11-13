// Floats kept in `xmm` registers between operations, against the same values computed through
// paths that keep them in general registers (a call's argument, a struct field, a `var` global):
// more live floats than `xmm` registers, floats live across calls, `f32` values handed from an
// `xmm` register to a general one and back (its bits must stay canonical), negation, every
// conversion, and branches on NaN fused with their comparison (a NaN takes the "not" side of
// every ordered test). Exit 0 when everything agrees.
struct Pair { a: f64, b: f32 }
var gF: f64 = 0.0;
var gS: f32 = 0.0;
idF x:f64 -> f64 { gF = x; return gF; }
idS x:f32 -> f32 { gS = x; return gS; }

// Twelve values live at once: more than the seven `xmm` registers the allocator has.
wide x:f64 -> f64 {
    a: f64 = x + 1.0; b: f64 = x * 2.0; c: f64 = x - 3.0; d: f64 = x / 4.0;
    e: f64 = a * b; f: f64 = c * d; g: f64 = a - d; h: f64 = b + c;
    i: f64 = e - f; j: f64 = g * h; k: f64 = a + b + c + d; l: f64 = e + f + g + h;
    return a + b + c + d + e + f + g + h + i + j + k + l;
}
wideRef x:f64 -> f64 {
    a: f64 = idF(x + 1.0); b: f64 = idF(x * 2.0); c: f64 = idF(x - 3.0); d: f64 = idF(x / 4.0);
    e: f64 = idF(a * b); f: f64 = idF(c * d); g: f64 = idF(a - d); h: f64 = idF(b + c);
    i: f64 = idF(e - f); j: f64 = idF(g * h); k: f64 = idF(idF(idF(a + b) + c) + d);
    l: f64 = idF(idF(idF(e + f) + g) + h);
    return idF(idF(idF(idF(idF(idF(idF(idF(idF(idF(idF(a + b) + c) + d) + e) + f) + g) + h) + i) + j) + k) + l);
}

// Across calls: values computed before a call and used after it.
across x:f64 -> f64 {
    a: f64 = x * 1.5;
    b: f64 = -a;
    c: f64 = idF(a) + b;
    return a * b + c;
}

single x:f32 -> f32 {
    y: f32 = x * 3.0;
    z: f32 = -y + 0.5;
    p: Pair = Pair { a: 1.0, b: z };
    w: f32 = idS(z) * p.b;
    return w - y;
}

// How many of the six ordered and equality tests hold, through fused branches.
tests x:f64 y:f64 -> long {
    n: long = 0;
    if (x < y) { n = n + 1; }
    if (x <= y) { n = n + 10; }
    if (x > y) { n = n + 100; }
    if (x >= y) { n = n + 1000; }
    if (x == y) { n = n + 10000; }
    if (x != y) { n = n + 100000; }
    while (x < y) { n = n + 1000000; x = x + 1.0; }
    return n;
}

main -> int {
    bad: long = 0;
    if (wide(5.0) != wideRef(5.0) || wide(-0.75) != wideRef(-0.75)) { bad = bad | 1; }
    if (across(2.0) != -9.0) { bad = bad | 2; }
    if (single(2.0) != 24.25) { bad = bad | 4; }
    zero: f64 = 0.0;
    nan: f64 = zero / zero;
    if (tests(nan, 1.0) != 100000 || tests(1.0, nan) != 100000 || tests(nan, nan) != 100000) { bad = bad | 8; }
    if (tests(1.0, 2.0) != 1100011 || tests(2.0, 2.0) != 11010 || tests(3.0, 2.0) != 101100) { bad = bad | 16; }
    // Conversions in and out of `xmm`.
    s: f64 = 0.0;
    for i in 0..1000 { s = s + (i as f64) * 0.5; }
    if ((s as long) != 249750 || ((s / 3.0) as f32) as f64 != idF(((idF(s) / 3.0) as f32) as f64)) { bad = bad | 32; }
    t: f32 = 0.0;
    for i in 0..100 { t = t + (i as f32); }
    if ((t as long) != 4950 || (t as f64) != 4950.0) { bad = bad | 64; }
    return bad as int;
}
