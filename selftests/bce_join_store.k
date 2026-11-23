// The bound is proved for `n` as the path set it, but the path then empties the vector it was
// proved against, in a call the optimizer does not copy in: the relation does not reach the join,
// and the loop's check stays.
#include <stdlib::vec>
drain v:&Vec<long> -> void { while (v.len() > 1) { v.pop(); } }
walk v:&Vec<long> w:&Vec<long> -> long {
    n: long = v.len();
    if (w.len() < n) {
        n = w.len();
        drain(v);
    }
    drain(w);
    t: long = 0;
    for i in 0..n { t = t + v[i]; }
    return t;
}
main -> int {
    v: Vec<long> = vec![1, 2, 3, 4];
    w: Vec<long> = vec![1, 2];
    f: fn(&Vec<long>, &Vec<long>) -> long = &walk;
    return f(&v, &w) as int;
}
