// Writing through a borrow binding into an immutable global is writing the global.
#include <stdlib::string>
enum E { Empty, Named(String) }
G: E = E.Named(stringOf("hello"));
grow -> long { match G { Named(s) { s.pushStr("!"); return s.len; } Empty { return 0; } } }
main -> int { return grow() as int; }
