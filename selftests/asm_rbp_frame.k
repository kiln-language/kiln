// An `asm` block that names `rbp` means the frame of the function it is written in. That function
// keeps a frame although nothing else in it needs one, and it is not copied into its caller: the
// `rbp` it stores is its own, below the caller's.
frameOf p:*long -> void { unsafe { asm { in rdi p; "mov [rdi], rbp" } } }
main -> int {
    mine: long = 0;
    theirs: long = 0;
    unsafe {
        asm { in rdi &mine; "mov [rdi], rbp" }
        frameOf(&theirs);
    }
    if (theirs == 0 || theirs >= mine) { return 1; }
    return 0;
}
