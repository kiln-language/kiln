// An inline asm block with an input and an output: the exit code comes back through a variable.
doubled n:long -> long {
    out: long = 0;
    unsafe {
        asm {
            in rcx n;
            "mov rax, rcx"
            "add rax, rcx"
            out out rax;
        }
    }
    return out;
}

main -> long { return doubled(13); }
