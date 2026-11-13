// What still works: a local assigned before it is lent; a Default type, built by its declaration;
// a slot filled through its raw address inside `unsafe`; and the swap once the local holds a value.
#include <stdlib::{core, vec, mem, string}>
var drops: long = 0;
struct R { id: long }
methods R for Drop { drop &self -> void { if (self.id != 0) { drops = drops + self.id; } } }
struct A { r: R, n: long }
struct P { x: long, y: long }
bump inout p:P -> void { p.x = p.x + 1; }
grow inout s:String -> void { s.pushStr("ab"); }
struct H { pending: R, list: Vec<A> }
methods H {
    commit &self -> void {
        a: A = A { r: R { id: 0 }, n: 1 };
        swapValues(&a.r, &self.pending);
        self.list.push(a);
    }
}
main -> int {
    p: P;
    p = P { x: 1, y: 2 };
    bump(&p);                       // 2
    s: String;                      // Default: built empty
    grow(&s);                       // 2
    q: P;
    unsafe { memcpy(&q as long, &p as long, sizeof(P)); }    // filled through its address
    {
        h: H = H { pending: R { id: 10 } };
        h.commit();
        h.pending = R { id: 20 };
        h.commit();
    }                               // drops 10 + 20 once each
    return (p.x + s.len + q.x + drops) as int;    // 2 + 2 + 2 + 30 = 36
}
