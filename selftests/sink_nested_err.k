// A field of a field of an owned local handed to a sink: only a local's direct fields are tracked.
// Refused (batch 9); it released `r` twice.
#include <stdlib::io>
struct Res { id: long }
methods Res for Drop { drop &self -> void { } }
struct H { r: Res, n: long }
struct O { h: H }
eat sink r:Res -> long { return r.id; }
main -> int { o: O = O { h: H { r: Res { id: 7 }, n: 1 } }; return eat(o.h.r) as int; }
