// A global declared without `var` is not written by an `asm` block's `out` either.
K: long = 5;

main -> int {
    unsafe { asm { in rax 7; out K rax; } }
    return K as int;
}
