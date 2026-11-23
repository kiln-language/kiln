// What a sink may take from a place, and the rewrites the refusals name, each release counted.
#include <stdlib::{io, string, vec, mem}>
var gDrops: long = 0;
struct Res { id: long }
methods Res for Drop { drop &self -> void { gDrops = gDrops + 1; } }
methods Res for Clone { clone &self -> Res { return Res { id: self.id }; } }
methods Res for Default { new -> Res { return Res { id: 0 }; } }
methods Res { consume self -> long { return self.id; } }
struct H { r: Res, n: long }
eat sink r:Res -> long { return r.id; }
owned -> long { h: H = H { r: Res { id: 1 }, n: 1 }; return eat(h.r); }         // a direct field of an owned local
byValue h:H -> long { return eat(h.r); }                                        // of a by-value parameter
byRecv h:H -> long { return h.r.consume(); }                                  // a by-value receiver of one
cloned h:&H -> long { return eat(h.r.clone()); }                                // a borrow: clone it
taken inout h:H -> long { return eat(take(&h.r)); }                             // or take it through the lend
strings xs:[String] -> long { dst: Vec<String>; dst.push(xs[0].clone()); return dst[0].len(); }
main -> int {
    if (owned() != 1) { return 1; }
    if (gDrops != 1) { return 2; }
    if (byValue(H { r: Res { id: 2 }, n: 0 }) != 2) { return 3; }
    if (gDrops != 2) { return 4; }
    if (byRecv(H { r: Res { id: 2 }, n: 0 }) != 2) { return 14; }
    if (gDrops != 3) { return 15; }
    if (true) { h: H = H { r: Res { id: 3 }, n: 0 }; if (cloned(h) != 3) { return 5; } }
    if (gDrops != 5) { return 6; }
    if (true) { h: H = H { r: Res { id: 4 }, n: 0 }; if (taken(&h) != 4) { return 7; } if (h.r.id != 0) { return 8; } }
    if (gDrops != 7) { return 9; }
    if (true) { v: Vec<Res>; v.push(Res { id: 5 }); if (eat(v.pop()) != 5) { return 10; } }
    if (gDrops != 8) { return 11; }
    src: Vec<String>; src.push(stringOf("hello"));
    if (strings(src.asSlice()) != 5) { return 12; }
    if (src[0] != "hello") { return 13; }
    return 0;
}
