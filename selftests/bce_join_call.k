// A call the optimizer cannot see into empties the vector the bound was read from.
#include <stdlib::vec>
empty v:&Vec<long> -> void { while (v.len() > 0) { v.pop(); } }
walk v:&Vec<long> m:long -> long {
    n: long = v.len();
    if (m < n) { n = m; }
    g: fn(&Vec<long>) -> void = &empty;
    g(v);
    t: long = 0;
    for i in 0..n { t = t + v[i]; }
    return t;
}
main -> int {
    v: Vec<long> = vec![1, 2, 3, 4];
    f: fn(&Vec<long>, long) -> long = &walk;
    return f(&v, 3) as int;
}
