// An operator through a borrow is the borrowed type's: `w == "center"` with `w: &String` is
// String's `Eq<str>`, and two `&P` compare, order, add and complement through P's `Eq`, `Ord`,
// `Add` and `Not` (they compared and added the ADDRESSES the borrows hold). Both directions where
// the right-hand type has the implementation. Each check adds its bit; all of them: 2047.
#include <stdlib::{cmp, string}>
struct P { x: long, y: long }
methods P for Copy { }
methods P for Eq<P> { eq &self o:P -> bool { return self.x == o.x && self.y == o.y; } }
methods P for Ord { cmp &self o:P -> int { if (self.x != o.x) { return (self.x - o.x) as int; } return (self.y - o.y) as int; } }
methods P for Add<P> { add self o:P -> P { return P { x: self.x + o.x, y: self.y + o.y }; } }
methods P for Sub<P> { sub self o:P -> P { return P { x: self.x - o.x, y: self.y - o.y }; } }
methods P for Not { not self -> P { return P { x: -self.x, y: -self.y }; } }
strs w:&String v:String -> long {
    n: long = 0;
    if (w == "center") { n = n | 1; }
    if (w != "left") { n = n | 2; }
    if (w == v) { n = n | 4; }
    if (v == w) { n = n | 8; }
    return n;
}
pts a:&P b:&P c:P -> long {
    n: long = 0;
    if (a < b) { n = n | 16; }
    if (a == c && !(a != c)) { n = n | 32; }
    if (c >= a && b > a && a <= c) { n = n | 64; }
    s: P = a + c;
    if (s.x == 2 && s.y == 4) { n = n | 128; }
    d: P = b - a;
    if (d.x == 2 && d.y == 2) { n = n | 256; }
    m: P = ~a;
    if (m.x == -1 && m.y == -2) { n = n | 512; }
    if (a != b) { n = n | 1024; }
    return n;
}
main -> int {
    s: String = stringOf("center");
    t: String = stringOf("center");
    p: P = P { x: 1, y: 2 };
    q: P = P { x: 3, y: 4 };
    r: P = P { x: 1, y: 2 };
    if (strs(&s, t) + pts(&p, &q, r) == 2047) { return 0; }
    return 1;
}
