// `match` on any expression: a call's result is held for the match and released after it (or
// taken apart by an arm that binds), a borrow (`v.at(i)`, `v[i]`) is matched where it lies, and
// `match &f()` borrows the temporary. A binding of such a match can be matched in turn.
#include <stdlib::{core, vec}>
var drops: long = 0;
struct R { id: long }
methods R for Drop { drop &self -> void { drops = drops + self.id; } }
enum Shape { Empty, Circle(long), Rect(long, long) }
enum Holder { Nothing, Has(R) }
enum Color: u8 { Red = 3, Green, Blue }
enum Wrap { W(Shape) }
mkShape n:long -> Shape {
    if (n == 0) { return Shape.Empty; }
    if (n == 1) { return Shape.Circle(4); }
    return Shape.Rect(n, 3);
}
mkHolder id:long -> Holder { return Holder.Has(R { id: id }); }
color n:long -> Color { if (n == 1) { return Color.Green; } return Color.Blue; }
main -> int {
    s: long = 0;
    match mkShape(2) { Rect(w, h) { s = s + w * h; } _ { } }               // 6
    match mkHolder(1) { Has(r) { s = s + r.id; } Nothing { } }             // 7; r released: drops 1
    if (drops != 1) { return 1; }
    match mkHolder(10) { Nothing { s = 100; } _ { } }                     // released after: 11
    if (drops != 11) { return 2; }
    hs: Vec<Holder> = vec![];
    hs.push(mkHolder(100));
    match hs.at(0) { Has(r) { s = s + r.id; } Nothing { } }               // a borrow: 107
    match hs[0] { Has(r) { s = s + r.id; } _ { } }                        // 207
    if (drops != 11) { return 3; }
    match &mkHolder(1000) { Has(r) { s = s + r.id / 100; } _ { } }        // 217; released after
    if (drops != 1011) { return 4; }
    match color(1) { Red { s = s + 1000; } Green { s = s + 3; } _ { } }   // 220
    match Wrap.W(mkShape(1)) { W(sh) { match sh { Circle(r) { s = s + r; } _ { } } } }   // 224
    return (s - 200) as int;      // 24
}
