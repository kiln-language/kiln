// Floats live across calls stay in `xmm12`-`xmm14`, which a Kiln function that uses one saves and
// restores: a caller holding several floats across calls to helpers that themselves hold floats
// across calls, float arguments passed from `xmm` registers (more than eight of them, so some go on
// the stack), and the answers checked against the same arithmetic in integers scaled by 1000.

var gV: long = 0;
dyn v:long -> long { gV = v; return gV; }

// Holds floats of its own across a call of its own (too long to inline, and called from two
// places): it uses `xmm12`-`xmm14` too, and must give its caller's back.
inner a:f64 b:f64 -> f64 {
    c: f64 = a * 2.0;
    d: f64 = b * 3.0;
    e: f64 = a + b;
    f: f64 = c - d;
    g: f64 = outer1(e);
    h: f64 = outer1(f);
    if (c > 1000000.0) { c = c * 0.5; d = d * 0.5; }
    if (d < -1000000.0) { e = e * 0.5; f = f * 0.5; }
    return c + d + e + f + g + h - f - 1.0;
}
outer1 x:f64 -> f64 { if (x > 1000000.0) { return 0.0; } return x + 1.0; }

many a:f64 b:f64 c:f64 d:f64 e:f64 f:f64 g:f64 h:f64 i:f64 j:f64 -> f64 {
    return a + 2.0 * b + 3.0 * c + 4.0 * d + 5.0 * e + 6.0 * f + 7.0 * g + 8.0 * h + 9.0 * i + 10.0 * j;
}

run n:long -> long {
    s: f64 = 0.0;
    t: f64 = 1.5;
    u: f64 = 0.25;
    w: f64 = 2.0;
    for k in 0..n {
        x: f64 = dyn(k) as f64;
        y: f64 = inner(x, t);
        z: f64 = inner(u, x);
        m: f64 = many(x, y, z, t, u, w, s * 0.0, 1.0, x, 2.0);
        s = s + y + z + m * 0.001 + t * u * w;
    }
    return (s * 1000.0) as long;
}

// The same in integers, thousandths.
innerL a:long b:long -> long {
    c: long = a * 2;
    d: long = b * 3;
    e: long = a + b;
    f: long = c - d;
    g: long = e + 1000;
    return c + d + e + f + g;     // h - f - 1 is 0: h is f + 1
}
runL n:long -> long {
    s: long = 0;
    for k in 0..n {
        x: long = dyn(k) * 1000;
        y: long = innerL(x, 1500);
        z: long = innerL(250, x);
        m: long = x + 2 * y + 3 * z + 4 * 1500 + 5 * 250 + 6 * 2000 + 7 * 0 + 8 * 1000 + 9 * x + 10 * 2000;
        s = s + y + z + m / 1000 + 750;
    }
    return s;
}

main -> int {
    a: long = run(dyn(50));
    b: long = runL(dyn(50));
    d: long = a - b;
    if (d < -50 || d > 50) { return 1; }
    return 0;
}
