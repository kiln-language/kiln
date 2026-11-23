// A method on `w` handed `w.s` to take: the receiver is lent for the whole call.
#include <stdlib::io>
#include <stdlib::string>
struct W { s: String }
methods W { eatS &self sink o:String -> void { println("{} {}", self.s, o); } }
main -> int { w: W = W { s: format("hi") }; w.eatS(w.s); return 0; }
