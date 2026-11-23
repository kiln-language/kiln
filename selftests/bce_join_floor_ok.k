// A start clamped at zero on the path where it could be negative: `i >= 0` on both paths into the
// loop, kept round it by `i + 1` under `i < xs.len`, so every element is read with no check, in a
// counter of each width.
pick xs:[long] from:long -> long {
    i: long = from;
    if (i < 0) { i = 0; }
    s: long = 0;
    while (i < xs.len) { s += xs[i]; i += 1; }
    return s;
}
pickInt xs:[long] from:int -> long {
    i: int = from;
    if (i < 0) { i = 0; }
    s: long = 0;
    while ((i as long) < xs.len) { s += xs[i as long]; i += 1; }
    return s;
}
main -> int {
    a: [long; 4] = [1, 2, 3, 4];
    f: fn([long], long) -> long = &pick;
    g: fn([long], int) -> long = &pickInt;
    if (f(a[..], -9) != 10 || f(a[..], 2) != 7 || f(a[..], 9) != 0) { return 1; }
    if (g(a[..], -9) != 10 || g(a[..], 3) != 4) { return 2; }
    return 0;
}
