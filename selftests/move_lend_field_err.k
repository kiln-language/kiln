// A field moved while the value holding it is lent to the same call.
#include <stdlib::io>
#include <stdlib::string>
struct W { s: String, t: String }
put r:W sink a:String -> void { println("{} {}", a, r.s); }
main -> int { v: W = W { s: format("ho"), t: format("x") }; put(v, v.s); return 0; }
