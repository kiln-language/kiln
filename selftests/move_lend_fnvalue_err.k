// A call through a fn value takes what its type marks `sink` and lends the rest.
#include <stdlib::io>
#include <stdlib::string>
take r:String sink s:String -> void { println("{} {}", r, s); }
main -> int { x: String = format("hello"); fv: fn(String, sink String) -> void = &take; fv(x, x); return 0; }
