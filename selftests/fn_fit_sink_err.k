// A lending callee stored where the fn type says `sink`: the caller gives the value up, the callee
// only borrows it, and nobody releases it. Refused (batch 9); it leaked.
#include <stdlib::io>
struct Res { id: long }
methods Res for Drop { drop &self -> void { } }
lend r:Res -> long { return r.id; }
main -> int { s: fn(sink Res)->long = &lend; r: Res = Res { id: 3 }; return s(r) as int; }
