// An owning field with no clone of its own blocks the derived clone of what holds it.
#include <stdlib::core>
struct Res { fd: long }
methods Res for Drop { drop &self -> void { } }
struct Holder { r: Res, n: long }
main -> int { h: Holder = Holder { r: Res { fd: 3 }, n: 1 }; g: Holder = h.clone(); return g.n as int; }
