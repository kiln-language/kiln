// A `var` global lent to a function that reads it where it lies, while something the call reaches
// writes it by name: the borrow would see the write. Refused at the call.
#include <stdlib::{io, vec}>
struct Reg { count: long, total: long }
var gReg: Reg = Reg { count: 0, total: 0 };
log -> void { gReg.count = gReg.count + 1; }
step -> void { log(); }
show r:Reg -> long { a: long = r.count; step(); return a + r.count; }
main -> long { return show(gReg); }
