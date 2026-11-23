// A slice's element read back from its spelling: a pointer and a fn value as elements.
// Each read as a struct (or a byte) named after what it held before.
inc x:long -> long { return x + 1; }
neg x:long -> long { return 0 - x; }

firstBytes ps:[*u8] -> long {
    t: long = 0;
    for p in ps { unsafe { t = t + (p[0] as long); } }
    return t;
}
calls fs:[fn(long) -> long] x:long -> long {
    t: long = 0;
    for f in fs { t = t + f(x); }
    return t;
}

main -> long {
    a: [u8; 2] = [7, 9];
    b: [u8; 1] = [20];
    ps: [*u8; 2] = [0 as *u8, 0 as *u8];
    unsafe { ps[0] = &a[1] as *u8; ps[1] = &b[0] as *u8; }
    if (firstBytes(ps[..]) != 29) { return 1; }
    fs: [fn(long) -> long; 2] = [&inc, &neg];
    if (calls(fs[..], 5) != 1) { return 3; }
    return 0;
}
