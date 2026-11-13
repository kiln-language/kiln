// The merge sort's shape: `hi = lo + 2 * width` capped at a constant, `lo = hi`, `i` from `lo`.
// Each sum is of values below a constant bound and never negative, so it is never negative
// either, and with `i < v.len()` in the loop's test no check of the read is left.
// ir-lacks: ranges::sweep panicIndex
// `i < m` and `m <= v.len()`: the read's `i < len` follows through m.
// ir-lacks: ranges::upto panicIndex
#include <stdlib::vec>
sweep v:Vec<long> -> long {
    s: long = 0;
    width: long = 1;
    while (width < 1000) {
        lo: long = 0;
        while (lo < 1000) {
            hi: long = lo + 2 * width;
            if (hi > 1000) { hi = 1000; }
            i: long = lo;
            while (i < hi && i < v.len()) { s = s + v.get(i); i = i + 1; }
            lo = hi;
        }
        width = width * 2;
    }
    return s;
}
upto v:Vec<long> m:long -> long {
    if (m > v.len()) { return 0; }
    s: long = 0;
    for i in 0..m { s = s + v.get(i); }
    return s;
}
main -> int {
    v: Vec<long>;
    for i in 0..1000 { v.push(i % 7); }
    if (sweep(v) != 29970 || upto(v, 10) != 24 || upto(v, 2000) != 0) { return 1; }
    return 0;
}
