// The same for a binding of a payload that owns something, a borrow since that rule went in: the
// per-call law compared the names the arguments are written with, and `r` is not `h`.
struct Res { n: long }
methods Res for Drop { drop &self -> void { } }
enum F { Full(Res), Empty }
struct H { f: F, k: long }
count h:&H -> long { match &h.f { Full(r) { return r.n; } _ { } } return 0; }
both inout r:Res h:&H -> long { r.n = r.n + 1; return count(h); }
run inout h:H -> long { match &h.f { Full(r) { return both(&r, h); } _ { } } return 0; }
main -> int { h: H = H { f: F.Full(Res { n: 1 }), k: 0 }; return run(&h) as int; }
