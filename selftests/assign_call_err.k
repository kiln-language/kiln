// A call's result is a value made for the statement, not a place.
next -> long { return 1; }
main -> int {
    next() = 3;
    return 0;
}
