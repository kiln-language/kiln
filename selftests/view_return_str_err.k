// The same view made a `str`: the cast keeps where it points.
#include <stdlib::{io, vec, string}>
leak -> str { v: Vec<u8>; v.push(104); v.push(105); v.push(33); return v.asSlice() as str; }
main -> int { s: str = leak(); println("{}", s); return 0; }
