// A destructure through a borrow follows the match's rule: a name bound to an element that owns
// nothing is a borrow of the element where it lies wherever the code after it writes through it,
// so the write lands in the tuple. A destructure of a value the function owns copies, as before.
// Exits with the number of the first check that fails.
struct P { x: long, y: long }
enum E { Pair((long, P)), Other }
struct H { pair: (long, P), n: long }
var gPair: (long, P) = (1, P { x: 1, y: 2 });

methods P { grow &self -> void { self.x = self.x * 2; } }
methods H {
    // `&self`: through a field.
    bump &self -> void { a, b = self.pair; b.x = b.x + 10; }
    // A method that writes `self`.
    grow2 &self -> void { a, b = self.pair; b.grow(); }
    // Only read: a copy, which reads the same.
    peek &self -> long { a, b = self.pair; return a + b.x; }
}
shift inout q:P -> void { q.y = q.y + 5; }
// A lend to `inout`, and a write in a loop.
viaLend inout h:H -> void { a, b = h.pair; shift(&b); for i in 0..3 { b.y = b.y + 1; } }
// Through a match binding of a tuple payload: the binding, the destructure's hidden local and the
// name all become borrows.
viaMatch inout e:E -> void { match e { Pair(t) { a, b = t; b.y = 7; } _ { } } }
viaGlobal -> void { a, b = gPair; b.x = 3; }
// An owned tuple: the names are copies.
owned -> long { t: (long, P) = (1, P { x: 1, y: 2 }); a, b = t; b.x = 9; c, d = t; return d.x; }

main -> int {
    h: H = H { pair: (5, P { x: 1, y: 2 }), n: 0 };
    h.bump();
    c1, d1 = h.pair;
    if (d1.x != 11) { return 1; }
    h.grow2();
    c2, d2 = h.pair;
    if (d2.x != 22) { return 2; }
    if (h.peek() != 27) { return 3; }
    viaLend(&h);
    c3, d3 = h.pair;
    if (d3.y != 10) { return 4; }
    e: E = E.Pair((1, P { x: 1, y: 2 }));
    viaMatch(&e);
    match e { Pair(t) { c4, d4 = t; if (d4.y != 7) { return 5; } } _ { return 5; } }
    viaGlobal();
    c5, d5 = gPair;
    if (d5.x != 3) { return 6; }
    if (owned() != 1) { return 7; }
    return 0;
}
