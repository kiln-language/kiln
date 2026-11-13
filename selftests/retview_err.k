// A trait object is {data, vtable} — a pointer to something it does not own. Returning one
// hands back a view of the frame being left.
#include <stdlib::core>
struct MySink { count: long }
methods MySink for Write { write &self ptr:long len:long -> long { return len; } }
leak -> Write { s: MySink = MySink { count: 0 }; return s; }
main -> int { w: Write = leak(); return 0; }
