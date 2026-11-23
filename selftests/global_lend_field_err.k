// A field of a `var` global lent to read, while the call reaches a write of that same field.
#include <stdlib::{io, vec}>
struct Reg { items: Vec<long>, count: long }
var gReg: Reg = Reg { items: vec![1, 2], count: 0 };
refill -> void { gReg.items.push(3); }
size xs:&Vec<long> -> long { n: long = xs.len(); refill(); return n + xs.len(); }
main -> long { return size(gReg.items); }
