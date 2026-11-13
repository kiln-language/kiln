two -> (long, long) { return (1, 2); }
main -> int {
    b: long = 0;
    a, b = two();
    return (a + b) as int;
}
