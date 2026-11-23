// `p` is a borrow of the payload of `e`, so lending it mutably to a call that also reads `e` is two
// overlapping accesses, as `both(&e, e)` would be: inside `both` a write through `q` would change
// what `r` was promised would hold still, which the optimizer trusts.
struct P { x: long, y: long }
enum E { Num(long), Pt(P) }
xOf e:&E -> long { match e { Pt(p) { return p.x; } _ { } } return -1; }
both inout q:P r:&E -> long { q.x = q.x + 100; return xOf(r); }
run inout e:E -> long { match e { Pt(p) { return both(&p, e); } _ { } } return 0; }
main -> int { e: E = E.Pt(P { x: 1, y: 2 }); return run(&e) as int; }
