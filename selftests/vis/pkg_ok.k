// `pkg` is reachable from another file of the SAME package, and `pub` from anywhere.
#include <helpers>
main -> int { return (shared() + open() + useAll()) as int; }
