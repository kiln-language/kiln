// `memcpy` reads and writes at raw addresses, so its declaration must say `unsafe`.
pub builtin memcpy dst:long src:long n:long -> void;
main -> long { return 0; }
