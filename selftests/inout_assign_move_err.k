#include <stdlib::io>
// Assigning a lent place moves the right-hand side in, and a borrow cannot be moved out of.
struct Res { n: long }
var gD: long = 0;
methods Res for Drop { drop &self -> void { gD = gD + 1; } }
take inout dst:Res inout src:Res -> void { dst = src; }
main -> int { a: Res = Res { n: 1 }; b: Res = Res { n: 2 }; take(&a, &b); return 0; }
