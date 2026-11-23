// The floor at the join is -5, not 0: `i` may be negative where it indexes, and the check stays.
pick xs:[long] from:long -> long {
    i: long = from;
    if (i < 0) { i = -5; }
    s: long = 0;
    while (i < xs.len) { s += xs[i]; i += 1; }
    return s;
}
main -> int {
    a: [long; 3] = [1, 2, 3];
    f: fn([long], long) -> long = &pick;
    return f(a[..], -2) as int;
}
