// `i < m` and `m <= len` do give i < len, but i starts at -1: the `i >= 0` half of the check
// stays, and the first read panics.
#include <stdlib::vec>
walk v:Vec<long> m:long -> long {
    if (m > v.len()) { return 0; }
    s: long = 0;
    i: long = -1;
    while (i < m) { s = s + v.get(i); i = i + 1; }
    return s;
}
main -> int {
    v: Vec<long>;
    for i in 0..4 { v.push(i); }
    return walk(v, 4) as int;
}
