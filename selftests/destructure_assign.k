// `a, b = t;` into names that are locals already assigns them: each target is stored into the way
// `x = v` stores (the old value released, the new one moved in), and the value is read whole
// before any target is written, so `leaf, pos = advance(leaf, pos)` steps a cursor. A target may
// be a field, an element, or an `inout` parameter. Every release is counted.
#include <stdlib::string>

var gDrops: long = 0;
struct Res { n: long }
methods Res for Drop { drop &self -> void { gDrops = gDrops + self.n; } }
mk n:long -> Res { return Res { n: n }; }

advance leaf:long pos:long -> (long, long) { return (leaf + pos, pos + 1); }
pairOf n:long -> (Res, long) { return (mk(n), n * 2); }
strs -> (String, String) { return (stringOf("left"), stringOf("right!")); }

struct Cursor { leaf: long, pos: long, held: Res }
methods Cursor {
    step &self -> void { self.leaf, self.pos = advance(self.leaf, self.pos); }
    refill &self n:long -> long { k: long = 0; self.held, k = pairOf(n); return k; }
}

fill inout r:Res n:long -> long { k: long = 0; r, k = pairOf(n); return k; }

main -> int {
    // Scalars, in a loop: the cursor steps.
    leaf: long = 0;
    pos: long = 1;
    for i in 0..4 { leaf, pos = advance(leaf, pos); }
    if (leaf != 10 || pos != 5) { return 1; }

    // Swapped through a tuple literal: both read before either is written.
    leaf, pos = (pos, leaf);
    if (leaf != 5 || pos != 10) { return 2; }

    // Owning: the old value is released when the new one moves in.
    {
        r: Res = mk(1);
        k: long = 0;
        r, k = pairOf(10);
        if (gDrops != 1 || r.n != 10 || k != 20) { return 3; }
    }
    if (gDrops != 11) { return 4; }
    gDrops = 0;

    // Strings, released and replaced.
    a: String = stringOf("x");
    b: String = stringOf("y");
    a, b = strs();
    if (a.len + b.len != 10) { return 5; }

    // Fields of a struct through `&self`, and an owning field.
    c: Cursor = Cursor { leaf: 0, pos: 1, held: mk(100) };
    c.step();
    c.step();
    if (c.leaf != 3 || c.pos != 3) { return 6; }
    if (c.refill(7) != 14 || gDrops != 100 || c.held.n != 7) { return 7; }

    // Fields of a local, and an element.
    xs: [long; 3];
    xs[1], c.pos = advance(4, 5);
    if (xs[1] != 9 || c.pos != 6) { return 8; }

    // `inout` parameters.
    q: Res = mk(1000);
    n: long = 0;
    n = fill(&q, 3);
    if (q.n != 3 || n != 6 || gDrops != 1100) { return 9; }

    // In an inner block, the outer locals are the targets.
    {
        leaf, pos = advance(1, 1);
    }
    if (leaf != 2 || pos != 2) { return 10; }
    return 0;
}
