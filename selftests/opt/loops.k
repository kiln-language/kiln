// A counter that starts at a value clamped at zero (`i = from; if (i < 0) { i = 0; }`) is known
// to be non-negative after the join and, stepped by one under `i < xs.len`, all round the loop:
// the bounds check of `xs[i]` goes. The loop's jump back is its test turned round, so no `jmp`
// is left in it. A body whose work is an `asm` block is copied into its caller, so `main` calls
// nothing for `bump`.
// ir-lacks: loops::scan bounds
// asm-lacks: loops::scan jmp
// asm-lacks: main mfn_loops$bump
scan xs:[long] from:long -> long {
    i: long = from;
    if (i < 0) { i = 0; }
    s: long = 0;
    while (i < xs.len) { s += xs[i]; i += 1; }
    return s;
}
bump x:long -> long { r: long = 0; unsafe { asm { in rax x; "add rax, 1" out r rax; } } return r; }
main -> int {
    xs: [long; 4] = [1, 2, 3, 4];
    f: fn([long], long) -> long = &scan;
    if (f(xs[..], -3) != 10 || f(xs[..], 1) != 9) { return 1; }
    if (bump(bump(40)) != 42) { return 2; }
    return 0;
}
