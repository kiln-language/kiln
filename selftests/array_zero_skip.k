// A local array written in full right after its declaration (by a literal, or a range loop over
// every index whose first statement stores the element) is not zero-filled first; anything less
// plain still is. Every element read back. Exit code 0.
fillTo n:long -> long {
    a: [long; 64];
    for i in 0..64 { a[i] = i * n; }
    t: long = 0;
    for x in a { t = t + x; }
    return t;
}
partly -> long {
    b: [long; 8];
    for i in 0..8 { if (i == 3) { break; } b[i] = 1; }
    t: long = 0;
    for x in b { t = t + x; }
    return t;                       // 3: the rest stayed zero
}
reads -> long {
    c: [long; 4];
    for i in 0..4 { c[i] = c[3] + 1; }   // reads `c` while filling it: zeroed, so every one is 1
    return c[0] + c[1] + c[2] + c[3];
}
lit -> long { d: [long; 3] = [7, 8, 9]; return d[0] + d[1] + d[2]; }
dirty -> long { junk: [long; 64]; for i in 0..64 { junk[i] = 99; } return junk[5]; }
main -> int {
    dirty();
    if (fillTo(2) != 4032) { return 1; }
    dirty();
    if (partly() != 3) { return 2; }
    if (reads() != 4) { return 3; }
    if (lit() != 24) { return 4; }
    return 0;
}
