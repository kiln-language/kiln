// The bound was read from a local slice, which is then pointed at a shorter one: the relation
// ends with the store into it, and the loop's check stays.
f a:[long] b:[long] k:long m:long -> long {
    xs: [long] = a;
    n: long = xs.len;
    if (k < n) { n = k; }
    xs = b[..m];
    t: long = 0;
    for i in 0..n { t = t + xs[i]; }
    return t;
}
main -> int {
    a: [long; 4] = [1, 2, 3, 4];
    b: [long; 4] = [5, 6, 7, 8];
    g: fn([long], [long], long, long) -> long = &f;
    return g(a[..], b[..], 3, 1) as int;
}
