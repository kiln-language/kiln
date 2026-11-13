// The exit releases ahead of a `return` are exempt; a write of the collection is still refused.
#include <stdlib::vec>
main -> int {
    v: Vec<long> = vec![1, 2, 3];
    for x in v { if (x == 2) { v.push(9); return 1; } }
    return 0;
}
