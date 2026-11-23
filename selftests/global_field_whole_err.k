// A function that assigns the whole of a `var` global writes every field of it, the walked one
// too.
#include <stdlib::vec>
struct Reg { items: Vec<long>, count: long }
var gReg: Reg = Reg { items: vec![1, 2], count: 0 };
reset -> void { gReg = Reg { items: vec![], count: 0 }; }
main -> int {
    t: long = 0;
    for x in gReg.items { if (x > 1) { reset(); } t = t + x; }
    return t as int;
}
