// The same bound through narrow unsigned arithmetic: `n` is a `u8` that wraps when it is
// incremented past 255, and the check on the index it leaves behind must stay.
pick x:[long] k:u8 -> long {
    n: u8 = 200;
    if (k < n) { n = k; }
    n = n + 100;
    return x[n as long];
}
main -> int {
    a: [long; 4] = [1, 2, 3, 4];
    f: fn([long], u8) -> long = &pick;
    return f(a[..], 180) as int;
}
