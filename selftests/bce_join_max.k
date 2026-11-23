// The larger of two lengths bounds neither slice: the check on `x[i]` stays, and fails. Called
// through a fn value, so the body runs as written and not folded into a caller's constants.
sum2 x:[long] y:[long] -> long {
    n: long = x.len;
    if (y.len > n) { n = y.len; }
    t: long = 0;
    for i in 0..n { t = t + x[i]; }
    return t;
}
main -> int {
    a: [long; 2] = [1, 2];
    b: [long; 4] = [1, 2, 3, 4];
    f: fn([long], [long]) -> long = &sum2;
    return f(a[..], b[..]) as int;
}
