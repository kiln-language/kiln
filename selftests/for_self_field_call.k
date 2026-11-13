// Inside `for a in self.cur.attrs`, a method of `self` that writes only other fields of `self`
// (directly, or through another method or a lend of another field) is allowed: the loop walks
// `self.cur.attrs`, and only a write to that may change what it reads.
#include <stdlib::{core, vec}>
struct A { name: long }
struct Tok { attrs: Vec<A>, kind: long }
struct T { cur: Tok, errors: long, seen: Tok }
bumpKind inout t:Tok -> void { t.kind = t.kind + 1; }
methods T {
    err &self -> void { self.errors = self.errors + 1; }
    errTwice &self -> void { self.err(); self.err(); }           // through another method
    markSeen &self -> void { bumpKind(&self.seen); }             // a lend of another field
    markKind &self -> void { self.cur.kind = self.cur.kind + 10; } // a sibling of the walked field
    check &self -> long {
        n: long = 0;
        for a in self.cur.attrs {
            if (a.name == 2) { self.err(); self.errTwice(); self.markSeen(); self.markKind(); }
            n = n + a.name;
        }
        return n;
    }
}
main -> int {
    t: T = T { cur: Tok { attrs: vec![], kind: 0 }, errors: 0, seen: Tok { attrs: vec![], kind: 0 } };
    t.cur.attrs.push(A { name: 1 });
    t.cur.attrs.push(A { name: 2 });
    t.cur.attrs.push(A { name: 4 });
    s: long = t.check();
    return (s + t.errors * 10 + t.seen.kind * 100 + t.cur.kind) as int;    // 7 + 30 + 100 + 10 = 147
}
