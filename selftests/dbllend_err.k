// A trait object may reach a `&self` method through its vtable, so lending one is a mutable
// access — the same value lent twice in one argument list overlaps itself.
#include <stdlib::core>
struct MySink { count: long }
methods MySink for Write { write &self ptr:long len:long -> long { self.count = self.count + len; return len; } }
both a:Write b:Write -> long { return 0; }
main -> int { s: MySink = MySink { count: 0 }; return both(s, s) as int; }
