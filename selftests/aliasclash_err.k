// A `pub` alias goes into one flat cross-module namespace, so claiming a name another module has
// already published there is a collision. Without `pub` it is this file's own and shadows theirs.
#include <stdlib::atomic>
pub type AtomicInt = long;
main -> int { return 0; }
