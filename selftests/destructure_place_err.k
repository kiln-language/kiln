two -> (long, long) { return (1, 2); }
main -> int {
    a: long = 0;
    a, 3 = two();
    return a as int;
}
