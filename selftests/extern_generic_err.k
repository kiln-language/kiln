// A generic has no symbol until its type is known: what gets emitted is `first_long`, stamped
// where the call is. There is nothing for a linker to find, so a bodyless declaration may not
// take type parameters — the definition has to cross as source.
#include <stdlib::vec>
pub first<T: Copy> v:Vec<T> -> T;
main -> int { return 0; }
