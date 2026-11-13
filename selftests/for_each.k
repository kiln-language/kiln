// `for x in xs` over a Vec, a slice, an array (a local's and a field's) and a variable holding an
// iterator; `for x in &xs` writing through each element. A struct element is read where it lies:
// the drop counter shows nothing is copied out and released, and the lending form's writes land
// in the collection. The same loops run at compile time, in a macro (before the ownership pass
// has made `x` a borrow) and in a global's initializer (after it).
#include <stdlib::io>
#include <stdlib::vec>
#include <stdlib::string>
#include <stdlib::iter>

var gDrops: long = 0;
struct Res { id: long, name: String }
methods Res for Drop { drop &self -> void { gDrops = gDrops + 1; } }
methods Res { bump &self -> void { self.id = self.id + 1; } idOf &self -> long { return self.id; } }
struct P { x: long, y: long }
struct G { cells: [long; 3], ps: [P; 2] }
enum Shape { Dot, Sq(long), Named(String) }
struct Bag<T> { items: Vec<T> }
methods Bag<T> { count &self -> long { n: long = 0; for x in self.items { n = n + 1; } return n; } }

countAll<T> v:Vec<T> -> long { n: long = 0; for x in v { n = n + 1; } return n; }
sumSlice xs:[long] -> long { s: long = 0; for x in xs { s = s + x; } return s; }
zeroX inout xs:[P] -> void { for p in &xs { p.x = 0; } }

macro doubled -> long {
    ps: Vec<P>; ps.push(P { x: 1, y: 2 }); ps.push(P { x: 3, y: 4 });
    for p in &ps { p.x = p.x * 2; }
    s: long = 0;
    for p in ps { s = s + p.x; }
    return s;
}
folded -> long {
    ps: Vec<P>; ps.push(P { x: 5, y: 0 }); ps.push(P { x: 6, y: 0 });
    for p in &ps { p.y = p.x + 1; }
    s: long = 0;
    for p in ps { s = s + p.y; }
    return s;
}
gFolded: long = folded();
var gG: G;

main -> int {
    v: Vec<long>; v.push(1); v.push(2); v.push(3);
    s: long = 0;
    for x in v { s = s + x; }
    if (s != 6) { return 1; }
    arr: [long; 4];
    arr[0] = 10; arr[1] = 20; arr[2] = 30; arr[3] = 40;
    t: long = 0;
    for a in arr { t = t + a; }
    if (t != 100 || sumSlice(arr[..]) != 100) { return 2; }
    gG.cells[0] = 1; gG.cells[1] = 2; gG.cells[2] = 3;
    c: long = 0;
    for x in gG.cells { c = c + x; }
    for p in &gG.ps { p.y = 7; }
    for p in gG.ps { c = c + p.y; }
    if (c != 20) { return 3; }

    rs: Vec<Res>;
    rs.push(Res { id: 1, name: format("a") });
    rs.push(Res { id: 2, name: format("bb") });
    n: long = 0;
    for r in rs { n = n + r.id + r.name.len; }
    if (n != 6 || gDrops != 0) { return 4; }          // read in place: nothing copied, nothing released
    for r in &rs { r.bump(); r.id = r.id * 10; }
    if (rs[0].id != 20 || rs[1].id != 30) { return 5; }
    k: long = 0;
    for r in rs { if (r.id == 20) { continue; } k = k + r.idOf(); }
    if (k != 30 || gDrops != 0) { return 6; }

    sh: Vec<Shape>;
    sh.push(Shape.Dot); sh.push(Shape.Sq(3)); sh.push(Shape.Named(format("hey")));
    area: long = 0;
    for e in sh { match e { Dot { area = area + 1; } Sq(q) { area = area + q * q; } Named(nm) { area = area + nm.len; } } }
    if (area != 13) { return 7; }

    pairs: long = 0;
    for a in v { for b in v { if (a < b) { pairs = pairs + 1; } } }
    if (pairs != 3) { return 8; }
    it: Range = range(0, 5);
    r5: long = 0;
    for i in it { r5 = r5 + i; }
    if (r5 != 10) { return 9; }
    b: Bag<String> = Bag { items: vec![] };
    b.items.push(format("x"));
    if (b.count() != 1 || countAll(rs) != 2) { return 10; }
    ps: [P; 2];
    ps[0] = P { x: 5, y: 1 }; ps[1] = P { x: 6, y: 1 };
    zeroX(&ps[..]);
    z: long = 0;
    for p in ps { z = z + p.x + p.y; }
    if (z != 2) { return 11; }
    if (doubled!() != 8 || gFolded != 13) { return 12; }
    f: long = 0;
    add: Fn() -> long = || { for x in v { f = f + x; } return f; };
    add();
    if (f != 6) { return 13; }
    w: Vec<long>;
    for x in v { if (x == 2) { break; } w.push(x * 100); }
    if (w.len() != 1) { return 14; }
    return 0;
}
