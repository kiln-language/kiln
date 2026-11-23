// A field of a `var` global lent to a function that walks it, while that function calls a
// writer of the same field.
#include <stdlib::vec>
struct Reg { items: Vec<long>, count: long }
var gReg: Reg = Reg { items: vec![1, 2], count: 0 };
bump -> void { gReg.count = gReg.count + 1; }
grow -> void { gReg.items.push(9); }
walk xs:&Vec<long> -> long { t: long = 0; for x in xs { bump(); grow(); t = t + x; } return t; }
main -> int { return walk(gReg.items) as int; }
