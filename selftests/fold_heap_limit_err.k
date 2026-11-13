// A fold that asks for more compile-time heap than the limit allows is refused before it takes
// any, and the refusal names the flag that raises the limit.
#include <stdlib::heap>
BIG: long = fill();
fill -> long { return malloc(314572800); }
main -> int { return BIG as int; }
