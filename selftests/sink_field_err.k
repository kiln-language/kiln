// A field of a borrowed value handed to a sink: its real owner releases it too. Refused (batch 9).
#include <stdlib::io>
struct Res { id: long }
methods Res for Drop { drop &self -> void { } }
struct H { r: Res, n: long }
eat sink r:Res -> long { return r.id; }
fromField h:&H -> long { return eat(h.r); }
main -> int { h: H = H { r: Res { id: 7 }, n: 1 }; return fromField(h) as int; }
