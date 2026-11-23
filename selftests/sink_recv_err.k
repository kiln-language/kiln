// A by-value receiver (`consume self`) reached through a borrow: the method takes the field out
// of a value the caller does not own. Refused (batch 9); it released `r` twice.
#include <stdlib::io>
struct Res { id: long }
methods Res for Drop { drop &self -> void { } }
methods Res { consume self -> long { return self.id; } }
struct H { r: Res, n: long }
peek h:&H -> long { return h.r.consume(); }
main -> int { h: H = H { r: Res { id: 7 }, n: 1 }; return peek(h) as int; }
