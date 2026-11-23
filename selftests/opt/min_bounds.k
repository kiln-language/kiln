// `n` is the smaller of two lengths, set on two paths that meet before the loop: every edge into
// the join leaves `n <= x.len` and `n <= y.len` true, which is all the loop's two checks need, so
// both go. The two pairs' words are read once, before the loop, which stores nothing.
// ir-lacks: min_bounds::common bounds
// ir-count: min_bounds::common ptrload 6
// ir-before: min_bounds::common ptrload [t0] .L2
// ir-before: min_bounds::common ptrload [t1] .L2
common x:[u8] y:[u8] -> long {
    n: long = x.len;
    if (y.len < n) { n = y.len; }
    for i in 0..n {
        if (x[i] != y[i]) { return i; }
    }
    return n;
}
main -> int {
    a: [u8; 4] = [1, 2, 3, 4];
    b: [u8; 3] = [1, 2, 9];
    if (common(a[..], b[..]) != 2 || common(b[..2], a[..]) != 2) { return 1; }
    f: fn([u8], [u8]) -> long = &common;
    if (f(a[..], a[..]) != 4) { return 2; }
    return 0;
}
