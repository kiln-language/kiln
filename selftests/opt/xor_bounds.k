// A value built of `^`, `|` and `>>` of values never negative, each below 2^k, is below 2^k too
// (`Flow.boundWalk`), so what is added to it does not wrap and stays never negative, and its
// division by a constant needs no rounding fix (no `shr ..., 63`). The bound is 2^k - 1 and no
// lower: `classify`'s `x` reaches 15, so its test is not decided.
// asm-lacks: xor_bounds::mix , 63
mix n:long -> long {
    s: long = 0;
    for i in 0..n {
        if (i >= 1000000) { return 0; }
        a: long = i * 3 + 1;
        b: long = a ^ (a >> 7);
        c: long = b + i;
        d: long = c | (c >> 3);
        s += d % 5 + c % 7;
    }
    return s;
}
classify a:long b:long -> long {
    x: long = (a & 15) ^ (b & 15);
    if (x < 8) { return 1; }
    return 2;
}
main -> int {
    f: fn(long) -> long = &mix;
    want: long = 0;
    for i in 0..100 {
        a: long = i * 3 + 1;
        b: long = a ^ (a >> 7);
        c: long = b + i;
        d: long = c | (c >> 3);
        want += d % 5 + c % 7;
    }
    if (f(100) != want) { return 1; }
    g: fn(long, long) -> long = &classify;
    if (g(8, 7) != 2 || g(1, 2) != 1) { return 2; }
    return 0;
}
