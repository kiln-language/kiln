// Through a cycle and a fn value: `ping` and `pong` call each other, a fn value may hold `bump`,
// and `bump` writes the walked global. The first call the body makes that reaches it is refused.
#include <stdlib::vec>
var gItems: Vec<long> = vec![1, 2, 3];
var gHook: fn(long)->void = &note;
note x:long -> void { }
bump x:long -> void { gItems.push(x); }
ping n:long -> long { if (n > 0) { return pong(n - 1); } return 0; }
pong n:long -> long { if (n > 5) { bump(n); gHook = &bump; } return ping(n); }
main -> int {
    t: long = 0;
    for x in gItems { t = t + ping(x); }
    for x in gItems { gHook(x); }
    return t as int;
}
