// A field of a field is not tracked: only a local's own fields can be moved out.
#include <stdlib::core>
struct Res { id: long }
methods Res for Drop { drop &self -> void { } }
struct Acc { s: Res, t: Res, n: long }
mk id:long -> Res { return Res { id: id }; }
mkAcc -> Acc { return Acc { s: mk(1), t: mk(2), n: 7 }; }
eat sink r:Res -> long { return r.id; }
look a:Acc -> long { return a.n; }
struct Outer { a: Acc, k: long }
main -> int { o: Outer = Outer { a: mkAcc(), k: 3 }; s: Res = o.a.s; return 0; }
