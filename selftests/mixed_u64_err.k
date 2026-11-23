// A `u64` and a signed type have no common type: an operation between them says which is meant.
f n:long -> long { return n - 1; }
main -> int {
    h: u64 = 7;
    n: long = f(0);
    if (h < n) { return 1; }
    return 0;
}
