// A `match` through a borrow binds a borrow of an owning payload; through an owned value it moves
// the payloads out, every one of them, and releases each exactly once. Every release is counted.
#include <stdlib::io>
#include <stdlib::heap>

var gDrops: long = 0;
struct Res { n: long }
methods Res for Drop { drop &self -> void { gDrops = gDrops + 1; } }

enum E { Empty, Full(Res), Pair(Res, Res), Mixed(Res, long) }

methods E {
    // `&self`: the binding is a borrow; matching twice releases nothing.
    peek &self -> long { match self { Full(r) { return r.n; } _ { return -1; } } }
    // ...and writing through it writes the matched value.
    bump &self -> void { match self { Full(r) { r.n = r.n + 1; } Pair(a, b) { a.n = a.n + 1; b.n = b.n + 1; } _ { } } }
}

// `inout`: the same.
grow inout e:E by:long -> long {
    match e { Full(r) { r.n = r.n + by; return r.n; } _ { return -1; } }
}

// A field reached through a borrow.
struct Holder { hits: long, e: E }methods Holder {
    look &self -> long {
        match self.e {
            Full(r) { self.hits = self.hits + 1; return r.n; }   // a disjoint field may be written
            _ { return -1; }
        }
    }
}

// By value: the payloads are the function's, both bindings of one arm move, and an arm that
// returns does not leave the next arm's test reading a moved value.
both e:E -> long {
    match e {
        Full(r) { return r.n; }
        Pair(a, b) { return a.n * 10 + b.n; }
        Mixed(r, k) { return r.n + k; }
        _ { }
    }
    return 0;
}
// A discarded owning slot is still released.
firstOf e:E -> long { match e { Pair(a, _) { return a.n; } _ { } } return 0; }

// A global is never this function's: matching one borrows too.
G: E = E.Full(Res { n: 40 });
fromGlobal -> long { match G { Full(r) { return r.n; } _ { return 0; } } }

// A tree whose box releases what it holds, walked through borrows.
struct TBox { p: *Tree }
enum Tree { Leaf(Res), Node(TBox, TBox) }
methods TBox for Drop { drop &self -> void { unsafe { gone: Tree = *self.p; free(self.p as long); } } }
methods TBox { at &self -> &Tree { unsafe { return *self.p; } } }
boxed t:Tree -> TBox { unsafe { p: *Tree = malloc(sizeof(Tree)) as *Tree; *p = t; return TBox { p: p }; } }
methods Tree {
    total &self -> long {
        match self {
            Leaf(r) { return r.n; }
            Node(l, rr) { return l.at().total() + rr.at().total(); }
        }
    }
}

main -> int {
    {
        e: E = E.Full(Res { n: 7 });
        if (e.peek() != 7 || e.peek() != 7) { return 1; }
        if (gDrops != 0) { return 2; }
        e.bump();
        if (grow(&e, 10) != 18) { return 3; }
        if (e.peek() != 18) { return 4; }
    }
    if (gDrops != 1) { return 5; }

    {
        h: Holder = Holder { hits: 0, e: E.Full(Res { n: 4 }) };
        if (h.look() + h.look() != 8 || h.hits != 2) { return 6; }        if (gDrops != 1) { return 7; }
    }
    if (gDrops != 2) { return 8; }

    if (both(E.Pair(Res { n: 3 }, Res { n: 4 })) != 34) { return 9; }
    if (gDrops != 4) { return 10; }
    if (both(E.Mixed(Res { n: 5 }, 6)) != 11) { return 11; }
    if (gDrops != 5) { return 12; }
    if (firstOf(E.Pair(Res { n: 1 }, Res { n: 2 })) != 1) { return 13; }
    if (gDrops != 7) { return 14; }

    {
        p: E = E.Pair(Res { n: 1 }, Res { n: 2 });
        p.bump();
        sum: long = both(p);
        if (sum != 23) { return 15; }
    }
    if (gDrops != 9) { return 16; }
    if (fromGlobal() + fromGlobal() != 80 || gDrops != 9) { return 20; }

    {
        t: Tree = Tree.Node(boxed(Tree.Leaf(Res { n: 1 })),
                            boxed(Tree.Node(boxed(Tree.Leaf(Res { n: 2 })), boxed(Tree.Leaf(Res { n: 3 })))));
        if (t.total() != 6 || t.total() != 6) { return 17; }
        if (gDrops != 9) { return 18; }
    }
    if (gDrops != 12) { return 19; }
    println("match through a borrow: {} releases, each once", gDrops);
    return 0;
}
