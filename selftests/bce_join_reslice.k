// The parameter the bound was read from is made shorter after the join: the check stays.
f x:[long] k:long -> long {
    n: long = x.len;
    if (k < n) { n = k; }
    x = x[..1];
    t: long = 0;
    for i in 0..n { t = t + x[i]; }
    return t;
}
main -> int {
    a: [long; 4] = [1, 2, 3, 4];
    g: fn([long], long) -> long = &f;
    return g(a[..], 3) as int;
}
