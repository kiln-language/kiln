// A fn value whose result is of another type. Refused (batch 9); the call read a `bool` as a long.
#include <stdlib::io>
isBig n:long -> bool { return n > 10; }
main -> int { f: fn(long)->long = &isBig; return f(50) as int; }
