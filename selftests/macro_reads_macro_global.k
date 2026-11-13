// A macro reading a global whose own initializer is a macro call (`vec![...]`): the macro waits
// for the global to be expanded and checked, then runs. Exit code: 2 + 3 = 5.
#include <stdlib::vec>
gT: Vec<long> = vec![1, 2];
gU: Vec<long> = vec![4, 5, 6];
macro readG -> Node { return Node.Int(gT.len() + gU.len()); }
main -> int { return readG!() as int; }
