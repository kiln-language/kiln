// `i * 3` with i in [-1, 2] is in [-3, 6]: it may be negative, and -3 panics.
var gI: long = -1;
pick i:long -> long {
    a: [long; 8];
    if (i < -1 || i > 2) { return 0; }
    return a[i * 3];
}
main -> int { return pick(gI) as int; }
