// A name declared again without a value is unassigned again: what a sibling scope assigned to
// its own variable of that name does not initialize this one.
main -> int {
    { x: long; x = 1; if (x > 5) { return 1; } }
    x: long;
    return x as int;
}
