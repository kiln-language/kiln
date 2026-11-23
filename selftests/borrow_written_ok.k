// Near misses of the law for a `&T` the callee writes through: two reads of one value, a written
// lend beside a disjoint field of the same struct, beside a distinct constant element, and through
// a fn value that holds only functions that read.
#include <stdlib::vec>
struct Pair { l: Vec<long>, r: Vec<long> }
struct Cnt { n: long }
both a:&Vec<long> b:&Vec<long> -> long { return a.len() * 10 + b.len(); }
move into:&Vec<long> from:&Vec<long> -> void { into.push(from.len()); }
add into:&Cnt from:&Cnt -> void { into.n = into.n + from.n; }
main -> int {
    v: Vec<long> = vec![1, 2, 3];
    s: long = both(&v, &v);
    p: Pair = Pair { l: vec![1], r: vec![1, 2] };
    move(&p.l, &p.r);
    cs: [Cnt; 2];
    cs[0] = Cnt { n: 1 }; cs[1] = Cnt { n: 5 };
    add(&cs[0], &cs[1]);
    rd: fn(&Vec<long>, &Vec<long>) -> long = &both;
    s = s + rd(&v, &v);
    return (s + p.l.len() + cs[0].n) as int;
}
