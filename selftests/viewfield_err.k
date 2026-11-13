// A view stored in a FIELD keeps a pointer to a frame the call will leave.
#include <stdlib::core>
struct MySink { count: long }
methods MySink for Write { write &self ptr:long len:long -> long { return len; } }
struct Holder { w: Write }
stash inout h:Holder v:Write -> void { h.w = v; }
main -> int { return 0; }
