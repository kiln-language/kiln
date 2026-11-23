// `5 - j` with j in [0, 10] is in [-5, 5]: it may be negative, and 5 - 8 panics.
var gJ: long = 8;
pick j:long -> long {
    a: [long; 8];
    if (j < 0 || j > 10) { return 0; }
    return a[5 - j];
}
main -> int { return pick(gJ) as int; }
