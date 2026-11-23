// `take` may release `s` before it returns, while `r` still points at the same buffer.
#include <stdlib::io>
#include <stdlib::string>
take r:String sink s:String -> void { println("{} {}", r, s); }
main -> int { x: String = format("hello"); take(x, x); return 0; }
