// A compound assignment stores into its left side too.
main -> int {
    a: long = 1;
    b: long = 2;
    (a, b) += (1, 1);
    return a as int;
}
