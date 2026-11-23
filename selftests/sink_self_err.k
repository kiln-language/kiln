// `self.r` in a `&self` method handed to a sink. Refused (batch 9); it released `r` twice.
#include <stdlib::io>
struct Res { id: long }
methods Res for Drop { drop &self -> void { } }
struct H { r: Res, n: long }
eat sink r:Res -> long { return r.id; }
methods H { give &self -> long { return eat(self.r); } }
main -> int { h: H = H { r: Res { id: 7 }, n: 1 }; return h.give() as int; }
