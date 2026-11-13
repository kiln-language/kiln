// A field of a value declared outside a loop cannot be moved inside it.
#include <stdlib::core>
struct Res { id: long }
methods Res for Drop { drop &self -> void { } }
struct Acc { s: Res, t: Res, n: long }
mk id:long -> Res { return Res { id: id }; }
mkAcc -> Acc { return Acc { s: mk(1), t: mk(2), n: 7 }; }
eat sink r:Res -> long { return r.id; }
look a:Acc -> long { return a.n; }
main -> int { acc: Acc = mkAcc(); i: long = 0; while (i < 2) { eat(acc.t); i = i + 1; } return 0; }
