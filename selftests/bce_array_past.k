// A fixed array walked one element too far: the loop bound is a constant, but not the array's
// length, so the last read keeps its check and fails it.
main -> int {
    a: [long; 4];
    for i in 0..4 { a[i] = i; }
    s: long = 0;
    for i in 0..5 { s = s + a[i]; }
    return s as int;
}
