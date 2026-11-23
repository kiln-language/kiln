// `n <= x.len` holds, but n is negative: an index below it is no index at all, and the
// (unsigned) check stays.
pick x:[long] k:long -> long {
    n: long = x.len;
    if (k < n) { n = k; }
    return x[n - 1];
}
main -> int {
    a: [long; 3] = [1, 2, 3];
    f: fn([long], long) -> long = &pick;
    return f(a[..], -4) as int;
}
