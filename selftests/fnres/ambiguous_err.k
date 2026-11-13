// A module that includes both cannot call the bare name: it is ambiguous, like a type name.
#include <a>
#include <b>
main -> int { return spell() as int; }
