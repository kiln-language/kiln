// A comparison's truth value goes straight into its destination's register (`emitCompare`): the
// register cleared before the comparison and its low byte set after it, not set in `al`, widened
// and copied. A `~` is made in its destination's register too.
// asm-lacks: set_in_place::marks movzx eax, al
// asm-lacks: set_in_place::inv not rax
marks xs:[long] k:long -> long {
    flags: [u8; 8];
    for i in 0..8 { flags[i] = 0; }
    for i in 0..xs.len { if (i < 8) { flags[i] = (xs[i] < k) as u8; } }
    n: long = 0;
    for i in 0..8 { n += (flags[i] as long) << i; }
    return n;
}
inv x:long y:long -> long { return (~x & y) + (~y ^ x); }
main -> int {
    a: [long; 4] = [1, 5, 2, 9];
    f: fn([long], long) -> long = &marks;
    if (f(a[..], 3) != 5) { return 1; }
    g: fn(long, long) -> long = &inv;
    if (g(12, 10) != ((~12 & 10) + (~10 ^ 12))) { return 2; }
    return 0;
}
