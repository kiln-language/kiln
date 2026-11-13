// A borrow binding cannot be handed to a parameter that takes it.
#include <stdlib::io>
struct Res { n: long }
methods Res for Drop { drop &self -> void { } }
enum E { Empty, Full(Res) }
keep sink r:Res -> long { return r.n; }
methods E { bad &self -> long { match self { Full(r) { return keep(r); } Empty { return 0; } } } }
main -> int { e: E = E.Full(Res { n: 1 }); return e.bad() as int; }
