// A view into a temporary: the String is released at the end of the statement that made it.
#include <stdlib::{io, string}>
leak -> str { return stringOf("hello").slice(0, 2); }
main -> int { println("{}", leak()); return 0; }
