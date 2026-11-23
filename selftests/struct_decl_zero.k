// A struct of plain data declared without a value starts as zero bytes, as an array does: a field
// no store reached reads 0, not whatever the last frame left on the stack.
struct P { a: long, b: long }
struct B { d: [long; 4] }
struct I { x: long, y: long }
struct O { i: I, n: long }

// Leaves its frame full of -1, where the next call's locals will sit.
dirty -> long {
    junk: [long; 64];
    for k in 0..64 { junk[k] = -1; }
    return junk[63];
}
partial -> long { p: P; p.a = 1; return p.b; }
element -> long { b: B; b.d[0] = 1; return b.d[3]; }
nested -> long { o: O; o.n = 1; return o.i.y; }
looped -> long {
    t: long = 0;
    for r in 0..3 { p: P; if (r == 0) { p.b = 5; } p.a = r; t = t + p.b; }
    return t;
}

main -> int {
    // Through fn values, so each runs in a frame of its own where `dirty` left its junk.
    fp: fn() -> long = &partial;
    fe: fn() -> long = &element;
    fn2: fn() -> long = &nested;
    fd: fn() -> long = &dirty;
    if (fd() != -1 || fp() != 0) { return 1; }
    if (fd() != -1 || fe() != 0) { return 2; }
    if (fd() != -1 || fn2() != 0) { return 3; }
    if (fd() != -1 || looped() != 5) { return 4; }
    return 0;
}
