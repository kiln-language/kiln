// An implementation that writes a parameter the trait only lends: a caller through the trait
// would not know it is written.
#include <stdlib::vec>
trait Fill { fill &self v:Vec<long> -> void; }
struct S { a: long }
methods S for Fill { fill &self inout v:Vec<long> -> void { v.push(self.a); } }
main -> int { s: S = S { a: 4 }; v: Vec<long>; s.fill(&v); return 0; }
