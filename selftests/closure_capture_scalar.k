#include <stdlib::{io}>

// Captures whose type is a scalar although they do not look like one: the `&self` of a scalar's,
// a `str`'s and a backed enum's methods holds the value itself, and a backed enum or a distinct
// type is spelled like a struct but is its integer. Each is read (and a local written) through
// the closure, at its own width.

viaBound<F: Fn() -> void> f:F -> void { f(); }
viaObj f:Fn() -> void -> void { f(); }

enum Color: long { Red = 3, Green = 5 }
enum Small: u8 { A = 7, B = 200 }
type Meters = distinct long;

methods long { twice &self -> long { n: long = 0; viaBound(|| { n = self * 2; }); return n; } }
methods str { doubled &self -> long { n: long = 0; viaObj(|| { n = self.len() * 2; }); return n; } }
methods Color { code &self -> long { n: long = 0; viaBound(|| { n = self as long; }); return n; } }
methods Small { code &self -> long { n: long = 0; viaObj(|| { n = self as long; }); return n; } }

// a narrow enum beside other fields, so a read at the wrong width would see them
struct W { tag: Small, pad: u8, rest: long }

main -> long {
    k: long = 21;
    if (k.twice() != 42) { return 1; }
    s: str = "abc";
    if (s.doubled() != 6) { return 2; }
    c: Color = Color.Green;
    if (c.code() != 5) { return 3; }
    n: long = 0;
    viaBound(|| { n = c as long; });
    if (n != 5) { return 4; }
    viaObj(|| { c = Color.Red; });
    if (c as long != 3) { return 5; }
    w: W = W { tag: Small.B, pad: 9, rest: -1 };
    t: Small = w.tag;
    viaBound(|| { n = t as long; });
    if (n != 200) { return 6; }
    viaObj(|| { t = Small.A; });
    if (t as long != 7 || t.code() != 7 || w.tag.code() != 200) { return 7; }
    m: Meters = 7 as Meters;
    viaBound(|| { n = m as long; });
    if (n != 7) { return 8; }
    b: u8 = 250;
    viaObj(|| { b = b + 3; });
    if (b != 253) { return 9; }
    return 0;
}
