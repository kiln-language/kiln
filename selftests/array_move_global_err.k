// A whole array moved out of a global, which keeps naming it. Refused (batch 9).
#include <stdlib::{io, string}>
struct Res { id: long }
methods Res for Drop { drop &self -> void { } }
methods Res for Default { new -> Res { return Res { id: 0 }; } }
var gA: [Res; 2];
main -> int { b: [Res; 2]; b = gA; return 0; }
