// Every target of a destructure is held to the same rule.
two -> (long, long) { return (1, 2); }
next -> long { return 1; }
main -> int {
    a: long = 0;
    a, next() = two();
    return a as int;
}
