// A `&self` method that only reads `self`, called on a `var` global, while it calls something that
// writes the global by name.
#include <stdlib::{io}>
struct Reg { count: long, total: long }
var gReg: Reg = Reg { count: 0, total: 0 };
tick -> void { gReg.total = gReg.total + 1; }
methods Reg {
    peek &self -> long { before: long = self.total; tick(); return self.total - before; }
}
main -> long { return gReg.peek(); }
