// A method that writes the walked field itself is still refused.
#include <stdlib::{core, vec}>
struct A { name: long }
struct Tok { attrs: Vec<A>, kind: long }
struct T { cur: Tok, errors: long }
methods T {
    drop1 &self -> void { self.cur.attrs.pop(); }
    check &self -> long {
        n: long = 0;
        for a in self.cur.attrs { self.drop1(); n = n + a.name; }
        return n;
    }
}
main -> int { t: T = T { cur: Tok { attrs: vec![], kind: 0 }, errors: 0 }; return t.check() as int; }
