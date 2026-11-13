// The body of `for x in v` may not change `v`: the loop reads its buffer and length once.
#include <stdlib::vec>
main -> int { v: Vec<long>; v.push(1); for x in v { if (x < 4) { v.push(x + 1); } } return 0; }
