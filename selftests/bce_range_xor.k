// `x ^ 8` with x in [0, 7] is in [0, 15]: not inside 9 elements, and 15 panics.
var gX: long = 7;
pick x:long -> long {
    a: [long; 9];
    if (x < 0 || x > 7) { return 0; }
    return a[x ^ 8];
}
main -> int { return pick(gX) as int; }
