// A lent parameter assigned as a whole writes the caller's value, as a field store does: `p = v`
// with `inout p`, and `self = v` in a `&self` method. For an owning type the old value is released
// (after the new one is built) and the new one moved in. Every release is counted.
#include <stdlib::io>

var gDrops: long = 0;
struct Res { n: long }
methods Res for Drop { drop &self -> void { gDrops = gDrops + 1; } }

struct P { x: long, y: long }
enum E { A(P), B(long) }
enum O { Has(Res), Not }

setP inout p:P -> void { p = P { x: 5, y: 6 }; }
setE inout e:E -> void { e = E.B(9); }
setE2 inout e:E v:E -> void { e = v; }
copyIn inout dst:P src:P -> void { dst = src; }        // a read borrow copied from
swapIn inout a:P inout b:P -> void { t: P = a; a = b; b = t; }
// The old value is read before it goes.
bumpRes inout r:Res -> void { r = Res { n: r.n + 1 }; }
// A move into a lent place.
putO inout o:O v:Res -> void { o = O.Has(v); }

methods P { reset &self -> void { self = P { x: 9, y: 8 }; } }
methods Res { renew &self k:long -> void { self = Res { n: k }; } }

// The same stores run by the compile-time evaluator: an immutable global is folded.
folded -> long {
    p: P = P { x: 1, y: 2 }; setP(&p);
    q: P = P { x: 0, y: 0 }; copyIn(&q, P { x: 3, y: 4 });
    swapIn(&p, &q);
    e: E = E.A(P { x: 1, y: 1 }); setE2(&e, E.B(7));
    k: long = 0;
    match e { B(v) { k = v; } _ { } }
    q.reset();
    return p.x * 1000 + q.x * 100 + k * 10 + q.y;      // 3000 + 900 + 70 + 8
}
FOLDED: long = folded();

main -> int {
    if (FOLDED != 3978 || folded() != 3978) { return 20; }
    p: P = P { x: 1, y: 2 }; setP(&p);
    if (p.x != 5 || p.y != 6) { return 1; }
    e: E = E.A(P { x: 1, y: 1 }); setE(&e);
    match e { B(v) { if (v != 9) { return 2; } } _ { return 3; } }
    f: E = E.A(P { x: 1, y: 1 }); setE2(&f, E.B(7));
    match f { B(v) { if (v != 7) { return 4; } } _ { return 5; } }
    q: P = P { x: 0, y: 0 }; copyIn(&q, P { x: 3, y: 4 });
    if (q.x != 3 || q.y != 4) { return 6; }
    swapIn(&p, &q);
    if (p.x != 3 || q.x != 5) { return 7; }
    p.reset();
    if (p.x != 9 || p.y != 8) { return 8; }

    r: Res = Res { n: 10 };
    bumpRes(&r);                    // the old Res is released: 1
    if (r.n != 11 || gDrops != 1) { return 9; }
    r.renew(20);                    // again: 2
    if (r.n != 20 || gDrops != 2) { return 10; }
    o: O = O.Not;
    putO(&o, Res { n: 30 });        // O.Not owns nothing
    if (gDrops != 2) { return 11; }
    putO(&o, Res { n: 31 });        // the Res 30 goes: 3
    if (gDrops != 3) { return 12; }
    match o { Has(x) { if (x.n != 31) { return 13; } } _ { return 14; } }
    return 0;
}
