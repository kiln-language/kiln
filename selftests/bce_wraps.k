// Two values that are never negative add to one that is: the sum wraps. A pass that took
// "non-negative plus non-negative" as non-negative would drop the `i < 0` half of the check.
#include <stdlib::vec>
main -> int {
    v: Vec<long>;
    for i in 0..4 { v.push(i); }
    big: long = 4611686018427387904;     // 2^62
    j: long = big + big;                 // 2^63 wraps to the most negative long
    k: long = 0;
    while (k < 1) { k = k + 1; }
    return v.get(j + k - 1) as int;
}
