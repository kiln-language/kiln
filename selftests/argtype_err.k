// A `str` is a {ptr,len} pair and a `long` is a word. Handing one where the other is declared
// read sixteen bytes off an eight-byte slot, and `f(7)` below segfaulted at run time.
local width s:str -> long { return s.len; }
main -> int { return width(7) as int; }
