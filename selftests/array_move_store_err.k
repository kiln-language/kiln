// An element stored into an array whose elements were moved away: the store would release one
// of them a second time. Refused (batch 9).
#include <stdlib::{io, string}>
struct Res { id: long }
methods Res for Drop { drop &self -> void { } }
methods Res for Default { new -> Res { return Res { id: 0 }; } }
main -> int { a: [Res; 2]; b: [Res; 2]; b = a; a[0] = Res { id: 1 }; return 0; }
