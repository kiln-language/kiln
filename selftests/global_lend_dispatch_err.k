// A dispatch reaches every implementation of the method: one of them writes the `var` global lent
// to the call.
#include <stdlib::{io}>
struct Reg { count: long }
var gReg: Reg = Reg { count: 0 };
trait Act { act &self -> void; }
struct Calm { n: long }
struct Wild { n: long }
methods Calm for Act { act &self -> void { } }
methods Wild for Act { act &self -> void { gReg.count = gReg.count + 1; } }
run r:Reg a:Act -> long { b: long = r.count; a.act(); return r.count - b; }
main -> long { c: Calm = Calm { n: 0 }; w: Wild = Wild { n: 0 }; w.act(); return run(gReg, c); }
