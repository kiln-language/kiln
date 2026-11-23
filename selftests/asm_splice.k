// A small body whose work is an `asm` block is copied into its callers like any other: its inputs
// become the caller's values, and an output goes to a slot of the caller's own, renamed for each
// copy, so two copies in one function keep their results apart. A block that defines a label
// stays a call: a second copy would define the label again. One that names `rsp` does too, since
// what it reads there is its own frame.
pub builtin atCompileTime -> bool;

addOne x:long -> long { r: long = 0; unsafe { asm { in rax x; "add rax, 1" out r rax; } } return r; }
swapHalves x:long -> long { r: long = 0; unsafe { asm { in rdx x; "rol rdx, 32" out r rdx; } } return r; }
// Copied into `both`, which copies `addOne` twice into itself.
both x:long y:long -> long { return addOne(x) * 1000 + addOne(y); }
// A label: called twice from `main`, so each call stays a call.
countdown n:long -> long {
    r: long = 0;
    unsafe { asm { in rcx n; "xor eax, eax" ".again:" "add rax, 2" "dec rcx" "jnz .again" out r rax; } }
    return r;
}
// A label and nothing that jumps to it: still a label a second copy would define again.
marker x:long -> long { r: long = 0; unsafe { asm { in rax x; ".mark:" "add rax, 3" out r rax; } } return r; }
// The stack: its own frame's.
depth -> long { r: long = 0; unsafe { asm { "mov rax, rsp" "and rax, 7" out r rax; } } return r; }
// A test of `atCompileTime` decided before the inliner weighs the body, so the loop it guards is
// gone and the block alone is what gets copied.
copyWord dst:*long src:*long -> void {
    if (atCompileTime()) {
        i: long = 0;
        while (i < 1) { unsafe { *dst = *src; } i = i + 1; }
        return;
    }
    unsafe { asm { in rdi dst; in rsi src; "mov rax, [rsi]" "mov [rdi], rax" } }
}

main -> int {
    if (addOne(41) != 42 || both(1, 2) != 2003 || both(10, 20) != 11021) { return 1; }
    if (swapHalves(1) != 4294967296) { return 2; }
    if (countdown(3) != 6 || countdown(5) != 10) { return 3; }
    if (depth() != 0) { return 4; }
    if (marker(1) + marker(2) != 9) { return 6; }
    a: long = 7;
    b: long = 0;
    c: long = 9;
    unsafe {
        copyWord(&b, &a);
        copyWord(&a, &c);
    }
    if (a != 9 || b != 7) { return 5; }
    return 0;
}
