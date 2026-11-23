// A binding the arm writes through is a borrow of the payload, so the arm may not also replace
// the matched value: the borrow would point into a payload that is gone.
struct P { x: long, y: long }
enum E { Num(long), Pt(P) }
swap inout e:E -> void { match e { Pt(p) { p.x = 1; e = E.Num(3); p.y = 2; } _ { } } }
main -> int { a: E = E.Pt(P { x: 1, y: 2 }); swap(&a); return 0; }
