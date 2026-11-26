#include <stdlib::{string}>

// A call in a loop that hands its callee a literal is weighed by what the literal leaves of
// the callee (`Relayout.foldTarget`): `bytesEqual` with four bytes on each side is its
// four-byte test, copied in, and its two loops are not; the literal's bytes are a constant.
// asm-lacks: fold_call::prefixed call mfn_bytes$bytesEqual
// asm-has: fold_call::prefixed 1031365995
prefixed s:str n:long -> long {
    hits: long = 0;
    for i in 0..n { if (strStartsWith(s, "key=")) { hits = hits + 1; } }
    return hits;
}
plain s:str -> long {
    if (strStartsWith(s, "key=")) { return 1; }
    return 0;
}
main -> int {
    if (prefixed("key=value", 3) != 3 || plain("kez=") != 0) { return 1; }
    if (prefixed("kez=value", 2) != 0 || plain("key=") != 1) { return 2; }
    return 0;
}
