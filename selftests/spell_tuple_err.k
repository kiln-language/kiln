// A tuple's element is `t.0` in a message, as in the source (it was `t.$0`).
#include <stdlib::vec>
f t:&(Vec<long>, long) -> long {
    for x in t.0 { t.0.push(x); }
    return 0;
}
main -> long { t: (Vec<long>, long) = (vec![1], 2); return f(&t); }
