// A write through a binding of a match through a borrow lands in the matched value, whatever the
// payload: a binding the arm writes through is a borrow of the payload where it lies, even when
// the payload owns nothing (it used to be a copy, and the write was lost). A match the function
// owns still binds the arm's own values. Exits with the number of the first check that fails.
#include <stdlib::vec>
struct P { x: long, y: long }
enum E { Num(long), Pt(P), Two(long, P) }
enum W { Wrap(E), Bare(long) }
struct H { st: E, n: long }
var gE: E = E.Pt(P { x: 1, y: 2 });

methods P {
    grow &self -> void { self.x = self.x * 2; }
}
methods E {
    // `&self`: the binding writes the receiver.
    bump &self -> void { match self { Pt(p) { p.x = p.x + 1; } _ { } } }
}
methods H {
    // `match self.st`: the hidden local the subject is read into is a borrow of `self.st` too.
    poke &self -> void { match self.st { Pt(p) { p.y = 1000; } _ { } } }
}
setPt inout e:E -> void { match e { Pt(p) { p.x = 99; } _ { } } }
setTwo inout e:E -> void { match e { Two(a, p) { p.y = 42; } _ { } } }
viaMethod inout e:E -> void { match e { Pt(p) { p.grow(); } _ { } } }
shift inout q:P -> void { q.y = q.y + 5; }
viaLend inout e:E -> void { match e { Pt(p) { shift(&p); } _ { } } }
bumpRef r:&P -> void { r.x = r.x + 1; }
viaRef inout e:E -> void { match e { Pt(p) { bumpRef(p); } _ { } } }
inLoop inout e:E -> void { match e { Pt(p) { for i in 0..3 { p.x = p.x + 10; } } _ { } } }
nested inout w:W -> void { match w { Wrap(inner) { match inner { Pt(p) { p.x = 7; } _ { } } } _ { } } }
throughRef r:&E -> void { match r { Pt(p) { p.y = 3; } _ { } } }
viaGlobal -> void { match gE { Pt(p) { p.x = 5; } _ { } } }
// Only read: the binding may stay a copy, and nothing changes.
readOnly e:E -> long { match e { Pt(p) { return p.x + p.y; } Num(n) { return n; } Two(a, p) { return a; } } }
// A by-value parameter is the function's own value, though it arrives as a borrow because the
// body only reads it: its bindings are the arm's own, as an owned match's are.
mine e:E -> long { match e { Pt(p) { p.x = 1000; p = P { x: 2000, y: 0 }; return p.x; } _ { } } return 0; }

xOf e:E -> long { match e { Pt(p) { return p.x; } Two(a, p) { return p.x; } _ { } } return -1; }
yOf e:E -> long { match e { Pt(p) { return p.y; } Two(a, p) { return p.y; } _ { } } return -1; }

main -> int {
    a: E = E.Pt(P { x: 1, y: 2 });
    setPt(&a);
    if (xOf(a) != 99) { return 1; }
    b: E = E.Two(5, P { x: 3, y: 4 });
    setTwo(&b);
    if (yOf(b) != 42 || xOf(b) != 3) { return 2; }
    c: E = E.Pt(P { x: 1, y: 2 });
    match &c { Pt(p) { p.x = 55; } _ { } }
    if (xOf(c) != 55) { return 3; }
    v: Vec<E>;
    v.push(E.Pt(P { x: 1, y: 2 }));
    v.push(E.Num(3));
    for e in &v { match e { Pt(p) { p.y = 77; } _ { } } }
    if (yOf(v.at(0)) != 77) { return 4; }
    for e in &v { setPt(&e); }
    if (xOf(v.at(0)) != 99) { return 5; }
    d: E = E.Pt(P { x: 10, y: 0 });
    d.bump();
    if (xOf(d) != 11) { return 6; }
    viaMethod(&d);
    if (xOf(d) != 22) { return 7; }
    viaLend(&d);
    if (yOf(d) != 5) { return 8; }
    viaRef(&d);
    if (xOf(d) != 23) { return 9; }
    inLoop(&d);
    if (xOf(d) != 53) { return 10; }
    h: H = H { st: E.Pt(P { x: 1, y: 2 }), n: 0 };
    h.poke();
    if (yOf(h.st) != 1000) { return 11; }
    w: W = W.Wrap(E.Pt(P { x: 1, y: 2 }));
    nested(&w);
    match w { Wrap(inner) { if (xOf(inner) != 7) { return 12; } } _ { return 12; } }
    throughRef(&d);
    if (yOf(d) != 3) { return 13; }
    viaGlobal();
    if (xOf(gE) != 5) { return 14; }
    if (readOnly(d) != 56) { return 15; }
    if (mine(d) != 2000 || xOf(d) != 53) { return 16; }
    // An owned match binds the arm's own values: writing them leaves the subject as it was.
    o: E = E.Pt(P { x: 1, y: 2 });
    match o { Pt(p) { p.x = 9; p = P { x: 8, y: 8 }; } _ { } }
    return 0;
}
