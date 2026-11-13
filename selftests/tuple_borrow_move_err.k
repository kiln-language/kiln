// Destructuring a borrowed tuple binds borrows: an owning element cannot be moved on from one.
#include <stdlib::core>
struct Res { n: long }
methods Res for Drop { drop &self -> void { } }
keep sink r:Res -> long { return r.n; }
struct H { p: (Res, long) }
methods H { take &self -> long { a, b = self.p; return keep(a); } }
main -> int { return 0; }
