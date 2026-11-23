// Tuples with a struct element handed back by generic methods and a plain function, taken apart
// into names and used whole. `Vec.at` (and `v[i]`) hands back a reference to the tuple, `Vec.get`
// a copy of it, `split` and `Pair.both` the tuple itself, through a result pointer. (Destructured,
// a reference was called as a function returning the tuple through a result pointer it never
// takes, and every argument was read one place off.)
#include <stdlib::vec>
struct P { x: long, y: long }
struct Pair<T> { a: long, b: T }
methods Pair<T> {
    both &self -> (long, T) { return (self.a, self.b); }
}
split n:long -> (long, P) { return (n, P { x: n + 1, y: n + 2 }); }
sum t:(long, P) -> long { return t.0 * 100 + t.1.x * 10 + t.1.y; }
main -> int {
    v: Vec<(long, P)>;
    v.push((1, P { x: 2, y: 3 }));
    v.push((4, P { x: 5, y: 6 }));
    a, b = v.at(1);
    if (v.len() != 2 || a != 4 || b.x != 5 || b.y != 6) { return 1; }
    c, d = v[0];
    if (c != 1 || d.y != 3) { return 2; }
    e, f = v.get(1);
    if (e != 4 || f.x != 5) { return 3; }
    g, h = split(7);
    if (g != 7 || h.x != 8 || h.y != 9) { return 4; }
    q: Pair<P> = Pair<P> { a: 10, b: P { x: 1, y: 2 } };
    i, j = q.both();
    if (i != 10 || j.x != 1 || j.y != 2) { return 5; }
    // Whole.
    if (sum(v.get(0)) != 123) { return 6; }
    w: (long, P) = v.at(1);
    if (sum(w) != 456) { return 7; }
    if (sum(split(1)) != 123) { return 8; }
    if (sum(q.both()) != 1012) { return 9; }
    // A name taken out of a reference is a borrow of its element where it is written through, so
    // changing it changes the vector; one taken out of a copy is a copy.
    b.x = 50;
    if (v[1].1.x != 50) { return 10; }
    f.x = 70;
    if (v[1].1.x != 50) { return 11; }
    return 0;
}
