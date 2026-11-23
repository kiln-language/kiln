// A whole array moved out of a field: nothing records the move. Refused (batch 9).
#include <stdlib::{io, string}>
struct Res { id: long }
methods Res for Drop { drop &self -> void { } }
methods Res for Default { new -> Res { return Res { id: 0 }; } }
struct H { v: [Res; 2] }
main -> int { h: H = H { }; b: [Res; 2]; b = h.v; return 0; }
