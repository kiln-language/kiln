// A counted loop over a vector reads each element unchecked: the loop's own test already says
// i < len, the length is the one the loop read (no store or call in between), and i >= 0
// because it starts at 0 and only ever grows by one below a bound.
// ir-lacks: bce_vec::sumv panicIndex
// ir-lacks: bce_vec::dbl panicIndex
// A read of the same index twice is checked once: one panic call left, from the first read.
// ir-has: bce_vec::twice panicIndex
#include <stdlib::vec>
sumv v:Vec<long> -> long { s: long = 0; for i in 0..v.len() { s = s + v.get(i); } return s; }
dbl inout v:Vec<long> -> void { for i in 0..v.len() { v.set(i, v.get(i) * 2); } }
twice v:Vec<long> h:long -> long {
    if (v.get(h) != 0 && v.get(h) != 7) { return v.get(h); }
    return 0;
}
main -> int {
    v: Vec<long>;
    for i in 0..10 { v.push(i); }
    dbl(&v);
    if (sumv(v) != 90 || twice(v, 3) != 6 || twice(v, 0) != 0) { return 1; }
    return 0;
}
