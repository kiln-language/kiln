pub unsafe builtin syscall nr:long args:...long -> long;
say -> long { unsafe { return syscall(1, 1, "x".ptr as long, 1); } }
S: long = say();
main -> long { return S; }
