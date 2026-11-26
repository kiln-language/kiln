// A `var` global built at startup may not point into the frame that builds it.
#include <stdlib::{io, write}>
struct Holder { w: Write }
var bad: Holder = Holder { w: FileOut { fd: 1 } };
main -> int { return 0; }
