// Writing to stdout: a string literal is a {ptr, len} pair, and the syscall takes both.
write s:str -> long {
    n: long = 0;
    unsafe {
        asm {
            in rsi s.ptr;
            in rdx s.len;
            "mov rax, 1"
            "mov rdi, 1"
            "syscall"
            out n rax;
        }
    }
    return n;
}

main -> int {
    write("hello from the self-hosted compiler\n");
    return 0;
}
