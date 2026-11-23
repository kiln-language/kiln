// A binding of a match through a borrow names the payload where it lies, so it cannot be given
// another value as a whole, even when the payload is a scalar the arm could have copied: the
// store would change only the copy. Replace the variant instead.
struct P { x: long, y: long }
enum E { Num(long), Pt(P) }
setNum inout e:E -> void { match e { Num(q) { q = 7; } _ { } } }
main -> int { a: E = E.Num(1); setNum(&a); return 0; }
