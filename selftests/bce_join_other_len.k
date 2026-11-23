// On one path `n` is loaded from the other slice's length, which is the longer: `n <= x.len` holds
// on the other path only, and the check on `x[i]` stays.
pick x:[long] y:[long] k:bool -> long {
    n: long = x.len;
    if (k) { n = y.len; }
    t: long = 0;
    for i in 0..n { t = t + x[i]; }
    return t;
}
main -> int {
    a: [long; 2] = [1, 2];
    b: [long; 4] = [1, 2, 3, 4];
    f: fn([long], [long], bool) -> long = &pick;
    return f(a[..], b[..], true) as int;
}
