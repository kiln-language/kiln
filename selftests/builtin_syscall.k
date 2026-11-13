// The `syscall` and `atCompileTime` builtins, declared here as the standard library will declare
// them: the compiler provides their bodies, found by the declaration. The same function runs at
// compile time (folding a global, through the evaluator's emulated mmap/munmap) and at run time
// (the real syscalls).
pub unsafe builtin syscall nr:long args:...long -> long;
pub builtin atCompileTime -> bool;

// Map a page, use it, give it back.
viaMmap seed:long -> long {
    unsafe {
        p: long = syscall(9, 0, 4096, 3, 0x22, -1, 0);
        if (p < 0) { return -1; }
        q: *long = p as *long;
        q[0] = seed;
        q[511] = seed + 1;
        r: long = q[0] + q[511];
        // Grown in place or moved, the contents come along.
        p2: long = syscall(25, p, 4096, 8192, 1, 0);
        q2: *long = p2 as *long;
        r = r + q2[511] - seed;
        syscall(11, p2, 8192);
        return r;
    }
}
where -> long {
    if (atCompileTime()) { return 1; }
    return 2;
}
FOLDED: long = viaMmap(20);        // 20 + 21 + 1 = 42, computed by the compiler
FOLD_WHERE: long = where();        // 1: the evaluator answers yes
main -> long {
    if (FOLD_WHERE != 1) { return 1; }
    if (where() != 2) { return 2; }
    if (viaMmap(20) != FOLDED) { return 3; }
    unsafe {
        s: str = "ok\n";
        if (syscall(1, 1, s.ptr as long, s.len) != 3) { return 4; }
    }
    return FOLDED;
}
