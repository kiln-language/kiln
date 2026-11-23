// A callee reached through a fn value has no summary: the call ends everything it could reach,
// `v.count` with it, and `v[2]` keeps its check and panics.
#include <stdlib::vec>
shrink v:&Vec<long> -> void { v.truncate(1); }
grow v:&Vec<long> -> void { v.push(9); }
pick f:fn(&Vec<long>) -> void -> long {
    v: Vec<long>;
    v.push(1); v.push(2); v.push(3);
    f(&v);
    return v[2];
}
main -> int {
    if (pick(&grow) != 3) { return 1; }
    return pick(&shrink) as int;
}
