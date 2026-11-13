// What `.clone()` is. A plain value's clone is the value (`Copy` implies `Clone`), so a scalar
// meets `T: Clone` and `Vec<long>.clone()` is Vec's deep clone; a struct that owns something and
// writes no clone gets one derived field by field, deep; a sum type's derived clone builds the
// variant that is live; and nothing is released twice (every release counted).
#include <stdlib::{string, vec, map, heap}>

var gLive: long = 0;
struct Tok { id: long }
methods Tok for Drop { drop &self -> void { gLive = gLive - 1; } }
methods Tok for Clone { clone &self -> Tok { gLive = gLive + 1; return Tok { id: self.id + 100 }; } }
mkTok id:long -> Tok { gLive = gLive + 1; return Tok { id: id }; }

struct Pair { name: String, t: Tok, n: long }              // derived, deep
struct Plain { x: long, y: int }                           // Copy
enum Shape { Dot, Circle(long), Named(String, Tok) }       // derived per variant
enum Small { A(long), B(int, int) }                        // Copy

dup<T: Clone> x:T -> T { return x.clone(); }

run -> long {
    bad: long = 0;
    a: Vec<long>; a.push(1); a.push(2);
    b: Vec<long> = a.clone();
    b.set(0, 99);
    if (a.get(0) != 1 || b.get(0) != 99 || b.len() != 2) { bad = bad + 1; }
    s: Vec<String>; s.push(stringOf("x"));
    t: Vec<String> = s.clone();
    t.at(0).push('y');
    if (s.at(0).len != 1 || t.at(0).len != 2) { bad = bad + 1; }
    m: HashMap<long, long>; m.put(1, 10);
    m2: HashMap<long, long> = m.clone();
    m2.put(1, 20);
    if (m.get(1) != 10 || m2.get(1) != 20) { bad = bad + 1; }

    k: long = 41;
    if (k.clone() + 1 != 42 || dup(k) != 41) { bad = bad + 1; }
    st: str = "abc";
    if (st.clone().len != 3) { bad = bad + 1; }
    ds: String = dup(stringOf("hey"));
    if (ds.len != 3) { bad = bad + 1; }

    p: Pair = Pair { name: stringOf("p"), t: mkTok(1), n: 7 };
    q: Pair = p.clone();
    q.name.push('!');
    if (p.name.len != 1 || q.name.len != 2 || q.t.id != 101 || q.n != 7 || p.t.id != 1) { bad = bad + 1; }
    pl: Plain = Plain { x: 3, y: 4 };
    pl2: Plain = pl.clone();
    if (pl2.x != 3 || pl2.y != 4) { bad = bad + 1; }

    shapes: Vec<Shape>;
    shapes.push(Shape.Dot); shapes.push(Shape.Circle(5)); shapes.push(Shape.Named(stringOf("n"), mkTok(2)));
    copies: Vec<Shape> = shapes.clone();
    sum: long = 0;
    for i in 0..copies.len() {
        c: Shape = copies.cloneAt(i);
        match c { Dot { sum = sum + 1; } Circle(r) { sum = sum + r * 10; } Named(n, t) { sum = sum + n.len * 100 + t.id * 1000; } }
    }
    if (sum != 1 + 50 + 100 + 202000) { bad = bad + 1; }
    sm: Small = Small.B(3, 4);
    sm2: Small = sm.clone();
    match sm2 { A(x) { bad = bad + 1; } B(x, y) { if (x + y != 7) { bad = bad + 1; } } }

    bx: Box<long> = newBox(5);
    bx2: Box<long> = bx.clone();
    if (bx2.get() != 5) { bad = bad + 1; }
    return bad;
}

main -> int {
    bad: long = run();
    if (gLive != 0) { bad = bad + 10; }
    return bad as int;
}
