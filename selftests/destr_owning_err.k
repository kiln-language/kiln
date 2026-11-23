// A name bound to an element that owns something is a borrow of it, as a match binding is, so the
// code after it may not replace the tuple: the old string is released, and `a` would read the freed
// buffer (it read the new one's bytes before this was refused).
#include <stdlib::string>
struct H { pair: (String, long) }
methods H { swap &self -> long { a, b = self.pair; self.pair = (format("zz"), 1); return a.len(); } }
main -> int { h: H = H { pair: (format("hello"), 2) }; return h.swap() as int; }
