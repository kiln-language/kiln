// `&` lends; a parameter that takes its argument (`sink`) cannot be lent to.
#include <stdlib::{core, vec}>
struct R { id: long }
methods R for Drop { drop &self -> void { } }
keep sink r:R -> long { v: Vec<R> = vec![]; v.push(r); return 1; }
main -> int { r: R = R { id: 1 }; return keep(&r) as int; }
