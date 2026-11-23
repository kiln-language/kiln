// And for a destructured name, a borrow of its element: `b` is part of `self.pair`.
struct P { x: long, y: long }
struct H { pair: (long, P) }
look h:&H -> long { a, b = h.pair; return b.x; }
both inout q:P h:&H -> long { q.x = q.x + 1; return look(h); }
methods H { run &self -> long { a, b = self.pair; return both(&b, self); } }
main -> int { h: H = H { pair: (1, P { x: 1, y: 2 }) }; return h.run() as int; }
