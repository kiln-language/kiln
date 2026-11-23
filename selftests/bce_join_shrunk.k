// `n <= v.len()` held where the two paths met, and stops holding when the vector shrinks: the
// check in the loop stays, and fails at the last index.
#include <stdlib::vec>
walk v:&Vec<long> m:long -> long {
    n: long = v.len();
    if (m < n) { n = m; }
    v.pop();
    t: long = 0;
    for i in 0..n { t = t + v[i]; }
    return t;
}
main -> int {
    v: Vec<long> = vec![1, 2, 3, 4];
    f: fn(&Vec<long>, long) -> long = &walk;
    return f(&v, 10) as int;
}
