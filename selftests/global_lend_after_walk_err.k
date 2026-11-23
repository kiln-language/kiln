// A `var` global lent to a function that walks it and, after the walk, calls something that
// writes it by name and reads it again: the borrow sees the write. (The walk rule alone allowed
// this; the law of exclusivity across the call does not.)
#include <stdlib::{io, vec}>
var gV: Vec<long>;
growV -> void { gV.push(4); }
walkThenGrow xs:&Vec<long> -> long { t: long = 0; for x in xs { t = t + x; } growV(); return t + xs.len(); }
main -> int { gV.push(1); gV.push(2); return walkThenGrow(gV) as int; }
