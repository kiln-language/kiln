// Compile-time code that writes to stderr and exits: what it wrote is the error.
pub unsafe builtin syscall nr:long args:...long -> long;
pub builtin exit status:long -> never;
boom msg:str -> never {
    unsafe { syscall(1, 2, "boom: ".ptr as long, 6); syscall(1, 2, msg.ptr as long, msg.len); }
    exit(134);
}
half n:long -> long { if (n % 2 != 0) { boom("odd"); } return n / 2; }
H: long = half(7);
main -> long { return H; }
