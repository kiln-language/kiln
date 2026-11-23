// The first target too: a call is not a place, wherever it stands in the list.
two -> (long, long) { return (1, 2); }
next -> long { return 1; }
main -> int {
    a: long = 0;
    next(), a = two();
    return a as int;
}
