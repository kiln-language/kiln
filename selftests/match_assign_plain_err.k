// The same for a payload that is a struct owning nothing, matched through a field of `&self`.
struct P { x: long, y: long }
enum E { Num(long), Pt(P) }
struct H { st: E }
methods H { reset &self -> void { match self.st { Pt(p) { p = P { x: 0, y: 0 }; } _ { } } } }
main -> int { h: H = H { st: E.Pt(P { x: 1, y: 2 }) }; h.reset(); return 0; }
