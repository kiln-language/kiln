// A method that writes `self` holds its receiver lent `inout`, so nothing it reaches may even read
// the `var` global it was called on by name.
#include <stdlib::{io}>
struct Reg { count: long, total: long }
var gReg: Reg = Reg { count: 0, total: 0 };
report -> long { return gReg.total; }
methods Reg {
    bump &self -> void { self.count = self.count + report(); }
}
main -> long { gReg.bump(); return gReg.count; }
