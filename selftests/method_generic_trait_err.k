// A trait method's implementation takes no type parameters of its own.
#include <stdlib::core>
trait Sh { show &self -> long; }
struct A { n: long }
methods A for Sh { show<T> &self -> long { return 1; } }
main -> int { return 0; }
