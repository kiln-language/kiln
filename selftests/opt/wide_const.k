// A constant past 32 bits is made once before a loop that reads it (`Flow.canHoist`), not on
// every turn: each `mov` of a ten-byte immediate runs once.
// ir-before: wide_const::zeros const 72340172838076673 .L0
// ir-before: wide_const::zeros const -9187201950435737472 .L0
zeros xs:[u64] -> long {
    n: long = 0;
    for i in 0..xs.len {
        w: u64 = xs[i];
        z: u64 = (w - 0x0101010101010101) & ~w & 0x8080808080808080;
        if (z != 0) { n += 1; }
    }
    return n;
}
main -> int {
    a: [u64; 3] = [0x1111111111111111, 0x1100111111111111, 0];
    f: fn([u64]) -> long = &zeros;
    if (f(a[..]) != 2) { return 1; }
    return 0;
}
