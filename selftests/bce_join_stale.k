// `i` is a copy of `from`'s old value; the test after it is of the new one. That `from >= 0` on
// the way in says nothing of `i`, which is -5 where it indexes, and the check stays.
pick xs:[long] from:long -> long {
    i: long = from;
    from = from + 10;
    if (from < 0) { i = 0; }
    s: long = 0;
    while (i < xs.len) { s += xs[i]; i += 1; }
    return s + from;
}
main -> int {
    a: [long; 3] = [1, 2, 3];
    f: fn([long], long) -> long = &pick;
    return f(a[..], -5) as int;
}
