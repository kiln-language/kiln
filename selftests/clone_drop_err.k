// A type with a `drop` of its own owns what sits behind its own pointers: a clone copied field
// by field would share it, and both values would release it. No clone is derived for one.
#include <stdlib::core>
struct Res { fd: long }
methods Res for Drop { drop &self -> void { } }
main -> int { a: Res = Res { fd: 3 }; b: Res = a.clone(); return b.fd as int; }
