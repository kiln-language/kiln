// A builtin's signature is held to the primitive's: the four-byte compare-and-swap takes and
// gives `int`s.
pub unsafe builtin atomicCas32 p:*int expected:long desired:int -> int;
main -> long { return 0; }
