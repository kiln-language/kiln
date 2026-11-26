// Rule (b) for views: a safe function may not keep a view into what it is lent. `v` is the
// caller's only for the call, and `h` outlives it.
#include <stdlib::{io, vec, string}>
struct Hold { s: str, n: long }
methods Hold { keepIt &self v:&Vec<u8> -> void { self.s = v.asSlice() as str; } }
fill inout h:Hold -> void { v: Vec<u8>; v.push(104); v.push(105); h.keepIt(&v); }
main -> int { h: Hold = Hold { s: "", n: 1 }; fill(&h); println("{}", h.s); return 0; }
