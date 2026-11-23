// A `var` global lent to a function that walks its parameter while calling a function that writes
// the global by name. Refused (batch 9); the walk read the block the push had freed.
#include <stdlib::{io, vec}>
var gV: Vec<long>;
grow -> void { for i in 0..200 { gV.push(1000 + i); } }
walk xs:&Vec<long> -> long { t: long = 0; for x in xs { grow(); t = t + x; } return t; }
main -> int { gV.push(1); gV.push(2); return walk(gV) as int; }
