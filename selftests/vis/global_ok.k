// `pkg` and `pub` globals are reachable from another file of the package; the private one through
// its own file's functions. 5 + 6 + (3 + 4) = 18.
#include <gdecl>
main -> int { return (gShared + gOpen + hiddenLen()) as int; }
