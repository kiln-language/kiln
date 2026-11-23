// Loop-invariant code motion (`flow.k` `hoist`): summing a Vec reads its count and its buffer
// once, before the loop, not on every trip; the counter and the element are still loaded in it.
// A loop whose body stores to the field it reads keeps the load.
// ir-before: licm::sumv ptrload [t0 + 16] .L0
// ir-before: licm::sumv ptrload [t0] .L0
// ir-after: licm::stored ptrload .L0
var gV: long = 0;
#include <stdlib::vec>
struct Box { n: long }
sumv v:&Vec<long> k:long -> long {
    s: long = 0;
    j: long = 0;
    while (j < k) { s = s + v[j]; j = j + 1; }
    return s;
}
stored -> long {
    b: Box = Box { n: 1 };
    s: long = 0;
    for i in 0..5 { s = s + b.n; b.n = b.n + 2; }
    return s;
}
main -> int {
    v: Vec<long>;
    for i in 0..10 { v.push(i); }
    if (sumv(&v, 10) != 45) { return 1; }
    if (stored() != 25) { return 2; }
    return 0;
}
