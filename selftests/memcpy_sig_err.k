// A builtin's signature is held to the primitive's: `memcpy` takes its length as a `long`.
pub unsafe builtin memcpy dst:long src:long n:int -> void;
main -> long { return 0; }
