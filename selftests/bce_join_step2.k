// A start that is non-negative on one path into the loop only (`flip` takes the other) is not
// taken to be non-negative: here it is -1 where it indexes, and the check stays.
pick xs:[long] from:long flip:bool -> long {
    i: long = from;
    if (from < 0) { i = 0; }
    if (flip) { i = from; }
    s: long = 0;
    while (i < xs.len) { s += xs[i]; i += 1; }
    return s;
}
main -> int {
    a: [long; 3] = [1, 2, 3];
    f: fn([long], long, bool) -> long = &pick;
    if (f(a[..], -1, false) != 6) { return 1; }
    return f(a[..], -1, true) as int;
}
