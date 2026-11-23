// The field a loop walks, written by a function the body calls, is still refused when the walk
// is of one field of a `var` global and the write names that field.
#include <stdlib::vec>
struct Reg { items: Vec<long>, count: long }
var gReg: Reg = Reg { items: vec![1, 2], count: 0 };
bump -> void { gReg.count = gReg.count + 1; }
grow -> void { gReg.items.push(9); }
main -> int {
    t: long = 0;
    for x in gReg.items { bump(); grow(); t = t + x; }
    return t as int;
}
