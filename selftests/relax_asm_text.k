// An `asm` block's lines are the programmer's, and may carry a comment: the emitter hands them to
// `relax.k` as text to be read, where its own lines are classified as they stand. The jumps of the
// loop around the block are still made short.
main -> int {
    t: long = 0;
    i: long = 0;
    while (i < 10) {
        r: long = 0;
        unsafe { asm { in rcx t; "mov rax, rcx ; the running total" "add rax, 1   ; plus one" out r rax; } }
        t = r;
        i = i + 1;
    }
    if (t != 10) { return 1; }
    return 0;
}
