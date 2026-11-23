// A counted loop of a few straight-line instructions runs two turns at a time (`Opt.unrollLoop`):
// its body twice between one test and the next, and once more after the loop for the turn an odd
// count leaves. Counts from none to seven, a constant bound, a sum read after the loop, and an
// inner loop entered again on each outer turn with its bound read once before both, and a bound
// of the smallest long, where the bound less one would wrap.
// asm-count: unroll::squares imul 3
// asm-count: unroll::fixed imul 3
squares xs:[long] -> long {
    t: long = 0;
    for x in xs { t += x * x; }
    return t;
}
var gK: long = 3;
fixed -> long {
    t: long = 0;
    for i in 0..9 { t += i * gK; }
    return t;
}
counted n:long -> long {
    c: long = 0;
    for i in 0..n { c += 3; }
    return c;
}
nested xs:[long] -> long {
    t: long = 0;
    for r in 0..3 { for j in 0..xs.len { t += xs[j] + r; } }
    return t;
}
main -> int {
    v: [long; 7] = [1, 2, 3, 4, 5, 6, 7];
    p: fn([long]) -> long = &squares;
    want: long = 0;
    for n in 0..8 {
        if (p(v[0..n]) != want) { return 1 + n as int; }
        if (n < 7) { want += v[n] * v[n]; }
    }
    q: fn() -> long = &fixed;
    if (q() != 108) { return 20; }
    m: fn([long]) -> long = &nested;
    if (m(v[..]) != 105) { return 21; }
    k: fn(long) -> long = &counted;
    if (k(0 - 9223372036854775807 - 1) != 0 || k(5) != 15) { return 22; }
    return 0;
}
