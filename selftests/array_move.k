// A whole fixed array of a Drop type is MOVED (batch 9): the destination's old elements are
// released, the source is moved-from and releases nothing at its scope's end. Every release is
// counted by value, so a double release or a leak changes the sum.
#include <stdlib::{io, string}>
var gDrops: long = 0;
struct Res { id: long }
methods Res for Drop { drop &self -> void { gDrops = gDrops + self.id; } }
methods Res for Default { new -> Res { return Res { id: 0 }; } }
methods Res for Clone { clone &self -> Res { return Res { id: self.id * 3 }; } }
struct Holder { v: [Res; 2], n: long }

pair x:long y:long -> long {             // a local into a local: b's old pair released, a's moved
    a: [Res; 2]; a[0] = Res { id: x }; a[1] = Res { id: y };
    b: [Res; 2]; b[0] = Res { id: 100 }; b[1] = Res { id: 1000 };
    b = a;
    return b[0].id + b[1].id;
}
declared -> long {                       // a declaration from an array
    a: [Res; 2]; a[0] = Res { id: 1 }; a[1] = Res { id: 2 };
    b: [Res; 2] = a;
    return b[1].id;
}
maybe c:bool -> long {                   // moved on one path: the flag decides at the scope's end
    a: [Res; 2]; a[0] = Res { id: 5 }; a[1] = Res { id: 6 };
    b: [Res; 2];
    if (c) { b = a; }
    return 0;
}
back -> long {                           // moved away, then given a whole array again
    a: [Res; 2]; a[0] = Res { id: 1 }; a[1] = Res { id: 2 };
    b: [Res; 2]; b = a;
    c: [Res; 2]; c[0] = Res { id: 10 }; c[1] = Res { id: 20 };
    a = c;
    return a[0].id + b[0].id;
}
inLoop n:long -> long {                  // declared in the loop, moved each time round
    t: long = 0;
    for i in 0..n {
        a: [Res; 2]; a[0] = Res { id: 1 }; a[1] = Res { id: 1 };
        b: [Res; 2]; b = a;
        t = t + b[0].id;
    }
    return t;
}
intoField -> long {                      // into a struct literal's field, and over a field
    a: [Res; 2]; a[0] = Res { id: 7 }; a[1] = Res { id: 8 };
    h: Holder = Holder { v: a, n: 1 };
    c: [Res; 2]; c[0] = Res { id: 70 }; c[1] = Res { id: 80 };
    h.v = c;
    return h.v[0].id + h.v[1].id;
}
cloned -> long {                         // the derived clone of a struct with such a field
    a: [Res; 2]; a[0] = Res { id: 1 }; a[1] = Res { id: 2 };
    h: Holder = Holder { v: a, n: 4 };
    k: Holder = h.clone();
    return k.v[0].id + k.v[1].id + k.n;
}
strings -> long {                        // a real owning element
    a: [String; 2]; a[0] = stringOf("ab"); a[1] = stringOf("cde");
    b: [String; 2]; b = a;
    b[0].pushStr("!");
    return b[0].len() + b[1].len();
}
main -> int {
    if (pair(1, 10) != 11) { return 1; }
    if (gDrops != 1111) { return 2; }                 // 100 + 1000 replaced, 1 + 10 at the end
    gDrops = 0;
    if (declared() != 2 || gDrops != 3) { return 3; }
    gDrops = 0;
    maybe(true);
    if (gDrops != 11) { return 4; }
    gDrops = 0;
    maybe(false);
    if (gDrops != 11) { return 5; }
    gDrops = 0;
    if (back() != 11 || gDrops != 33) { return 6; }
    gDrops = 0;
    if (inLoop(3) != 3 || gDrops != 6) { return 7; }
    gDrops = 0;
    if (intoField() != 150 || gDrops != 165) { return 8; }   // 7 + 8 replaced, 70 + 80 at the end
    gDrops = 0;
    if (cloned() != 13 || gDrops != 12) { return 9; }        // 1 + 2, and the clones' 3 + 6
    if (strings() != 6) { return 10; }
    return 0;
}
