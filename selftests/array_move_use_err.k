// A whole array of a Drop type read after it was moved. Refused (batch 9).
#include <stdlib::{io, string}>
struct Res { id: long }
methods Res for Drop { drop &self -> void { } }
methods Res for Default { new -> Res { return Res { id: 0 }; } }
main -> int { a: [Res; 2]; b: [Res; 2]; b = a; return a[0].id as int; }
