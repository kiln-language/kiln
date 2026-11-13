// A type with a `drop` of its own cannot be partly moved: its `drop` must still run, and it reads
// every field (Rust's rule).
#include <stdlib::core>
var gN: long = 0;
struct Res { id: long }
methods Res for Drop { drop &self -> void { } }
struct Own { s: Res, n: long }
methods Own for Drop { drop &self -> void { gN = gN + self.n; } }
main -> int { o: Own = Own { s: Res { id: 1 }, n: 2 }; s: Res = o.s; return 0; }
