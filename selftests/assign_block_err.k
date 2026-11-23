// A block is a statement here: it has no value to store into.
main -> int {
    x: long = 0;
    { x } = 1;
    return x as int;
}
