// A generic function's instance takes and lends as its signature says.
#include <stdlib::string>
gtake<T> r:T sink s:T -> void { }
main -> int { x: String = format("hello"); gtake(x, x); return 0; }
