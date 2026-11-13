// A global whose initializer calls a macro declared LATER in the page is held back and
// retried once the macro can run, the way a function is. Exit code 45.
#include <stdlib::ast>
#include <stdlib::vec>
G: Vec<long> = both![4, 5];
main -> int { return (G.get(0) * 10 + G.get(1)) as int; }
macro both src:str -> Node { return Node.Call("vecOf", parseEach(splitTopLevel(src, "both!"), "long")); }
