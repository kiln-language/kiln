// The ownership walk goes on past an error to the next function too.
#include <stdlib::io>
struct Res { n: long }
methods Res for Drop { drop &self -> void { } }
gone r:Res -> Res { return r; }
a1 -> long { r: Res = Res { n: 1 }; s: Res = gone(r); return r.n + s.n; }
a2 inout r:Res -> long { x: Res = r; return x.n; }
main -> int { return 0; }
