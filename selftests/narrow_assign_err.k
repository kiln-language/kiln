// An assignment is held to the same rule as a declaration.
f n:long -> long { return n + 1; }
main -> int {
    i: int = 0;
    i = f(5);
    return i;
}
