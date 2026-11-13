// The trait lends `v` `inout`; an implementation that takes it as a read borrow does not fit.
#include <stdlib::vec>
trait Fill { fill &self inout v:Vec<long> -> void; }
struct S { a: long }
methods S for Fill { fill &self v:Vec<long> -> void { } }
main -> int { s: S = S { a: 4 }; v: Vec<long>; s.fill(v); return 0; }
