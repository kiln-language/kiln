// A loop whose last block a conditional branch reaches (an `if` with no `else` just before the
// jump back) has that jump turned into its test as well (`markRotations`, `--no-rotate-join`):
// both loops below end in a turned test (a label and a branch each), and no `jmp` is left.
// asm-count: rotate_join::marks .LR 4
// asm-lacks: rotate_join::marks jmp
marks n:long -> long {
    sieve: [int; 1000];
    for i in 0..1000 { sieve[i] = 0; }
    c: long = 0;
    for p in 2..n {
        if (sieve[p] == 0) {
            c += 1;
            m: long = p + p;
            while (m < n) { sieve[m] = 1; m += p; }
        }
    }
    return c;
}
main -> int {
    if (marks(1000) != 168 || marks(30) != 10) { return 1; }
    return 0;
}
