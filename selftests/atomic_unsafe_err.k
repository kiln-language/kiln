// An atomic reads or writes through the raw address it is handed, so its builtin must be declared
// `unsafe`, as `syscall` must.
pub builtin atomicLoad p:*long -> long;
main -> long { return 0; }
