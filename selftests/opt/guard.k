// A callee that begins `if (test) { return; }` keeps its call, but its test is copied to the call
// site and the call made only when the test fails: `Vec.push`'s growth check is a compare.
// ir-has: guard::fill .GD
// ir-count: guard::fill call vec::RawVec_long_reserve 1
#include <stdlib::vec>
fill n:long -> long { v: Vec<long>; for i in 0..n { v.push(i); } return v.len(); }
main -> int {
    if (fill(1000) != 1000) { return 1; }
    return 0;
}
