// A borrow binding cannot be reassigned as a whole: that would only re-aim the borrow.
#include <stdlib::io>
struct Res { n: long }
methods Res for Drop { drop &self -> void { } }
enum E { Empty, Full(Res) }
methods E { bad &self -> long { match self { Full(r) { r = Res { n: 2 }; return r.n; } Empty { return 0; } } } }
main -> int { e: E = E.Full(Res { n: 1 }); return e.bad() as int; }
