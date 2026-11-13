// A `str`'s `.ptr` and `.len` handed to a call are its words copied out, not a write of it:
// `putStr` hands `s.ptr` to `Write.write`, and a slice of an immutable global may still be
// handed to `putStr`.
#include <stdlib::io>
#include <stdlib::fmt>
#include <stdlib::string>
local HEX: str = "0123456789abcdef";
hexOf w:Write n:long -> void {
    d: long = n & 15;
    putStr(w, HEX[d..d+1]);
}
lenOf p:*u8 n:long -> long { return n; }
main -> int {
    s: String;
    hexOf(s, 11); hexOf(s, 4); hexOf(s, 255);
    k: long = 0;
    unsafe { k = lenOf(HEX.ptr, HEX.len); }
    if (!s.eq("b4f") || k != 16) { return 1; }
    return 0;
}
