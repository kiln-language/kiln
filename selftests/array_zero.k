// A local array declared without a value starts as zero bytes, whatever the stack held: small
// ones (unrolled stores), big ones (`rep stosq`), lengths that are not a whole number of words,
// arrays of structs, one declared in a loop (zeroed every time round), and the evaluator agrees.
struct P { x: long, y: int }

dirty -> long {
    junk: [long; 64];
    i: long = 0;
    while (i < 64) { junk[i] = 0 - 1 - i; i = i + 1; }
    return junk[63];
}
sumSmall -> long {
    a: [long; 8];
    b: [u8; 13];
    s: long = 0;
    i: long = 0;
    while (i < 8) { s = s + a[i]; i = i + 1; }
    i = 0;
    while (i < 13) { s = s + (b[i] as long); i = i + 1; }
    return s;
}
sumBig -> long {
    a: [long; 300];
    c: [u8; 1027];
    ps: [P; 20];
    s: long = 0;
    i: long = 0;
    while (i < 300) { s = s + a[i]; i = i + 1; }
    i = 0;
    while (i < 1027) { s = s + (c[i] as long); i = i + 1; }
    i = 0;
    while (i < 20) { s = s + ps[i].x + (ps[i].y as long); i = i + 1; }
    return s;
}
inLoop -> long {
    s: long = 0;
    k: long = 0;
    while (k < 3) {
        a: [long; 4];
        s = s + a[0] + a[3];
        a[0] = 7; a[3] = 9;
        k = k + 1;
    }
    return s;
}
FOLDED: long = sumSmall() + sumBig() + inLoop();

main -> int {
    if (FOLDED != 0) { return 1; }
    dirty();
    if (sumSmall() != 0) { return 2; }
    dirty();
    if (sumBig() != 0) { return 3; }
    dirty();
    if (inLoop() != 0) { return 4; }
    return 0;
}
