// A macro runs a body before the compiler has decided which bindings are borrows, and it has to
// agree with the compiled program: a write through a binding of a borrowed value lands in that
// value when a macro runs it, as it does at run time; a binding of an owned value, and one nothing
// writes through, are copies in both. Each value is computed by a macro and by the program, and the
// two have to match. Exits with the number of the first check that fails.
#include <stdlib::vec>
struct P { x: long, y: long }
struct Res { n: long }
methods Res for Drop { drop &self -> void { } }
enum E { Num(long), Pt(P) }
enum F { Full(Res), Empty }
struct H { st: E, pair: (long, P) }
setPt inout e:E -> void { match e { Pt(p) { p.x = 99; } _ { } } }
xOf e:E -> long { match e { Pt(p) { return p.x; } _ { } } return -1; }
methods H { poke &self -> void { match self.st { Pt(p) { p.y = 1000; } _ { } } a, b = self.pair; b.x = 5; } }
viaInout -> long { a: E = E.Pt(P { x: 1, y: 2 }); setPt(&a); return xOf(a); }
viaAmp -> long { a: E = E.Pt(P { x: 1, y: 2 }); match &a { Pt(p) { p.y = 5; } _ { } } match a { Pt(p) { return p.y; } _ { } } return -1; }
viaSelf -> long { h: H = H { st: E.Pt(P { x: 1, y: 2 }), pair: (1, P { x: 0, y: 0 }) }; h.poke(); c, d = h.pair; match h.st { Pt(p) { return p.y + d.x; } _ { } } return -1; }
viaOwning -> long { f: F = F.Full(Res { n: 1 }); match &f { Full(r) { r.n = 42; } _ { } } match &f { Full(r) { return r.n; } _ { } } return -1; }
owned -> long { a: E = E.Pt(P { x: 1, y: 2 }); match a { Pt(p) { p.x = 50; } _ { } } return xOf(a); }
// Only read, after the variant it lies in was replaced: through a borrow, but a copy, which still
// reads 1.
readIn inout h:H -> long { r: long = 0; match h.st { Pt(p) { h.st = E.Num(3); r = p.x; } _ { } } return r; }
readOnly -> long { h: H = H { st: E.Pt(P { x: 1, y: 2 }), pair: (1, P { x: 0, y: 0 }) }; return readIn(&h); }
// A tuple taken apart through a reference: the name written through is its element.
viaAt -> long { v: Vec<(long, P)>; v.push((1, P { x: 1, y: 2 })); a, b = v.at(0); b.x = 8; return v.at(0).1.x; }
macro ctInout -> long { return viaInout(); }
macro ctAmp -> long { return viaAmp(); }
macro ctSelf -> long { return viaSelf(); }
macro ctOwning -> long { return viaOwning(); }
macro ctOwned -> long { return owned(); }
macro ctRead -> long { return readOnly(); }
macro ctAt -> long { return viaAt(); }
main -> int {
    if (ctInout!() != viaInout() || viaInout() != 99) { return 1; }
    if (ctAmp!() != viaAmp() || viaAmp() != 5) { return 2; }
    if (ctSelf!() != viaSelf() || viaSelf() != 1005) { return 3; }
    if (ctOwning!() != viaOwning() || viaOwning() != 42) { return 4; }
    if (ctOwned!() != owned() || owned() != 1) { return 5; }
    if (ctRead!() != readOnly() || readOnly() != 1) { return 6; }
    if (ctAt!() != viaAt() || viaAt() != 8) { return 7; }
    return 0;
}
