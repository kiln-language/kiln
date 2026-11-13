// A global that cannot be computed at compile time is an error naming what stopped it -- a `var`
// would initialize at startup instead. Here: a clock, which is a syscall.
#include <stdlib::time>
T: long = now().secs;
main -> int { return 0; }
