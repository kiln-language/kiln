// A fn value returned where a fn type of another arity is promised. Refused (batch 9).
#include <stdlib::io>
twice n:long -> long { return n * 2; }
give -> fn(long, long)->long { return &twice; }
main -> int { g: fn(long, long)->long = give(); return g(5, 6) as int; }
