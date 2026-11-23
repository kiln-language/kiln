// A whole array moved inside a loop out of one declared before it. Refused (batch 9): the
// second time round it is moved-from.
#include <stdlib::{io, string}>
struct Res { id: long }
methods Res for Drop { drop &self -> void { } }
methods Res for Default { new -> Res { return Res { id: 0 }; } }
main -> int { a: [Res; 2]; for i in 0..2 { b: [Res; 2]; b = a; } return 0; }
