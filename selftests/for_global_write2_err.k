// The same through two calls and a method: `step` calls `grow`, which writes the global.
#include <stdlib::vec>
struct Bag { v: Vec<long> }
var gBag: Bag = Bag { v: vec![1, 2] };
grow -> void { gBag.v.clear(); }
step n:long -> long { if (n > 1) { grow(); } return n; }
main -> int {
    t: long = 0;
    for x in gBag.v { t = t + step(x); }
    return t as int;
}
