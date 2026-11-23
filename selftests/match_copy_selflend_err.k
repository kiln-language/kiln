// A method that writes `self` called on the matched value while an arm holds a borrow of its
// payload. `touch` writes `self.st` only through a binding of its own match, which the write
// masks see because that binding writes the payload it borrows.
struct P { x: long, y: long }
enum E { Num(long), Pt(P) }
struct H { st: E }
methods H {
    touch &self -> void { match self.st { Pt(p) { p.x = 0; } _ { } } }
    both &self -> void { match self.st { Pt(q) { q.y = 2; self.touch(); } _ { } } }
}
main -> int { h: H = H { st: E.Pt(P { x: 1, y: 2 }) }; h.both(); return 0; }
