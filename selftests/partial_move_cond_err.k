// A field moved on one path only: reading it afterwards is refused.
#include <stdlib::core>
struct Res { id: long }
methods Res for Drop { drop &self -> void { } }
struct Acc { s: Res, t: Res, n: long }
mk id:long -> Res { return Res { id: id }; }
mkAcc -> Acc { return Acc { s: mk(1), t: mk(2), n: 7 }; }
eat sink r:Res -> long { return r.id; }
look a:Acc -> long { return a.n; }
main -> int { acc: Acc = mkAcc(); c: bool = acc.n > 3; if (c) { eat(acc.s); } return acc.s.id as int; }
