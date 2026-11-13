pub builtin syscall nr:long args:...long -> long;
main -> long { return syscall(39); }
