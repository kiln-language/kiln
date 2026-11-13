// A generic sum type's static method needs its instance said somewhere: by an argument, or by
// where the result goes.
#include <stdlib::option>
methods Option<T> { nothing -> Option<T> { return Option.None; } }
main -> int { Option.nothing(); return 0; }
