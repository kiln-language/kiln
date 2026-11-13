pub unsafe builtin syscall nr:long args:...long -> long;
pid -> long { unsafe { return syscall(39); } }
P: long = pid();
main -> long { return P; }
