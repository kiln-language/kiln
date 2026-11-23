// A write through a binding of an immutable global's payload writes the global.
struct P { x: long, y: long }
enum E { Num(long), Pt(P) }
G: E = E.Pt(P { x: 1, y: 2 });
poke -> void { match G { Pt(p) { p.x = 5; } _ { } } }
main -> int { poke(); return 0; }
