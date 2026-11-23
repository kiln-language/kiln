// What a call may do with one value in two arguments: plain data handed to a `sink` is a copy,
// an argument evaluated before the call (`x.len()`, `x.clone()`) lends nothing across it, and
// disjoint fields do not overlap. Exits with the number of the first check that fails.
#include <stdlib::string>
struct P { x: long, y: long }
struct W { s: String, t: String }
takeP r:P sink s:P -> long { return r.x + s.y; }
takeL n:long sink s:String -> long { return n + s.len(); }
takeS r:String sink s:String -> long { return r.len() + s.len(); }
takeF r:String sink s:String -> long { return r.len() * 10 + s.len(); }
main -> int {
    p: P = P { x: 1, y: 2 };
    if (takeP(p, p) != 3) { return 1; }
    x: String = format("hello");
    if (takeL(x.len(), x) != 10) { return 2; }
    y: String = format("abc");
    if (takeS(y.clone(), y) != 6) { return 3; }
    w: W = W { s: format("ab"), t: format("xyz") };
    if (takeF(w.s, w.t) != 23) { return 4; }
    return 0;
}
