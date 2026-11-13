// `i < m` and `m <= len + 1`: no chain says i < len, and the last read is past the end.
#include <stdlib::vec>
walk v:Vec<long> m:long -> long {
    if (m > v.len() + 1) { return 0; }
    s: long = 0;
    for i in 0..m { s = s + v.get(i); }
    return s;
}
main -> int {
    v: Vec<long>;
    for i in 0..4 { v.push(i); }
    return walk(v, 5) as int;
}
