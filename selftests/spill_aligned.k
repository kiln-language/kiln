// The `@spill` function is entered as any function is, with the stack aligned for its frame,
// whatever the alignment where the check failed: inside a body with a frame, rsp is a multiple of
// 16. Exit 70 when it is, 78 when it is eight off.
pub unsafe builtin syscall nr:long args:...long -> long;
@spill keep -> void {
    r: long = 0;
    unsafe { asm { "mov rax, rsp" out r rax; } }
    unsafe { syscall(60, 70 + (r & 15)); }
}
main -> int {
    a: [long; 4];
    for i in 0..4 { a[i] = i; }
    s: long = 0;
    for i in 0..5 { s = s + a[i]; }
    return s as int;
}
