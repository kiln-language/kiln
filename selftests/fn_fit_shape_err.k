// A fn value of another shape stored in a fn-typed place. Refused (batch 9); any fn type fitted
// any other, so `f(5)` called `look` with the integer 5 as the address of a Res and crashed.
#include <stdlib::io>
struct Res { id: long }
look r:Res -> long { return r.id; }
main -> int { f: fn(long)->long = &look; return f(5) as int; }
