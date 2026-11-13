// After a field is moved out, the value as a whole is gone: lending it is refused.
#include <stdlib::core>
struct Res { id: long }
methods Res for Drop { drop &self -> void { } }
struct Acc { s: Res, t: Res, n: long }
mk id:long -> Res { return Res { id: id }; }
mkAcc -> Acc { return Acc { s: mk(1), t: mk(2), n: 7 }; }
eat sink r:Res -> long { return r.id; }
look a:Acc -> long { return a.n; }
main -> int { acc: Acc = mkAcc(); s: Res = acc.s; return look(acc) as int; }
