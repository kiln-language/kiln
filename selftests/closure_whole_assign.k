#include <stdlib::{io, vec}>

// A struct a closure captured, assigned whole inside the body: the store writes the variable the
// closure was built over (a local, an `inout` parameter, a `&self`), as a store to one of its
// fields does. The old value is released once, the new one kept. And read whole, the bytes copied
// are the variable's, not the closure's pointer to it.

viaBound<F: Fn() -> void> f:F -> void { f(); }
viaObj f:Fn() -> void -> void { f(); }

struct P { x: long, y: long }
struct Wrap { p: P, n: long }
struct Tree { items: Vec<long>, count: long }

var gDrops: long = 0;
struct Res { id: long }
methods Res for Drop { drop &self -> void { gDrops = gDrops + self.id; } }
struct Holder { r: Res, n: long }

replaceIn inout t:Tree -> void { viaObj(|| { t = Tree { items: vec![5, 6, 7], count: 3 }; }); }

methods P {
    reset &self -> void { viaBound(|| { self = P { x: 0, y: 0 }; }); }
}

main -> long {
    p: P = P { x: 1, y: 2 };
    viaBound(|| { p = P { x: 5, y: 6 }; });
    if (p.x != 5 || p.y != 6) { return 1; }
    viaObj(|| { p = P { x: p.y, y: p.x }; });
    if (p.x != 6 || p.y != 5) { return 2; }
    o: P = P { x: 30, y: 40 };
    viaBound(|| { p = o; });
    if (p.x != 30 || p.y != 40) { return 3; }
    p.reset();
    if (p.x != 0 || p.y != 0) { return 4; }
    // and read whole: into a local, a literal's field, an array literal
    got: long = 0;
    viaBound(|| { q: P = o; w: Wrap = Wrap { p: o, n: 1 }; xs: [P; 2] = [o, q]; got = q.x + w.p.y + xs[1].y; });
    if (got != 110) { return 9; }

    t: Tree = Tree { items: vec![], count: 0 };
    viaBound(|| { t = Tree { items: vec![40], count: 1 }; });
    if (t.items.len() != 1 || t.items[0] != 40 || t.count != 1) { return 5; }
    replaceIn(&t);
    if (t.items.len() != 3 || t.items[2] != 7 || t.count != 3) { return 6; }

    {
        h: Holder = Holder { r: Res { id: 1 }, n: 0 };
        viaObj(|| { h = Holder { r: Res { id: 10 }, n: 1 }; });
        if (gDrops != 1 || h.n != 1) { return 7; }
    }
    if (gDrops != 11) { return 8; }
    println("closure_whole_assign");
    return 0;
}
