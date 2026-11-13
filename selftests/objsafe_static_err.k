// A method with no receiver has nothing to dispatch on: behind a vtable there is no value to
// find the table from. Still a perfectly good BOUND, where the type is known.
trait Maker { make -> Self; }
struct P { v: long }
methods P for Maker { make -> P { return P { v: 1 }; } }
main -> int { p: P = P.make(); m: Maker = p; return 0; }
