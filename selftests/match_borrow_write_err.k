// A match arm that holds a borrow of the payload may not lend the matched value mutably.
#include <stdlib::io>
var gDrops: long = 0;
struct Res { n: long }
methods Res for Drop { drop &self -> void { gDrops = gDrops + 1; } }
enum E { Empty, Full(Res) }
methods E {
    reset &self -> void { self = E.Empty; }
    bad &self -> long { match self { Full(r) { self.reset(); return r.n; } Empty { return 0; } } }
}
main -> int { e: E = E.Full(Res { n: 1 }); return e.bad() as int; }
