// A call through a fn value reaches any function whose address the program takes: one of them
// writes the `var` global lent to the call.
#include <stdlib::{io}>
struct Reg { count: long }
var gReg: Reg = Reg { count: 0 };
clear -> void { gReg.count = 0; }
quiet -> void { }
var gHook: fn() -> void = &quiet;
watch r:Reg -> long { a: long = r.count; gHook(); return a - r.count; }
main -> long { gHook = &clear; gReg.count = 5; return watch(gReg); }
