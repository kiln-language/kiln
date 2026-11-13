// A macro that exits: its stderr text is the error, as a panic in a macro is.
pub unsafe builtin syscall nr:long args:...long -> long;
pub builtin exit status:long -> never;
macro check n:long -> long {
    if (n > 9) { unsafe { syscall(1, 2, "check: too big\n".ptr as long, 15); } exit(1); }
    return n;
}
main -> long { return check!(12); }
