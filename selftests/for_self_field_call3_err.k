// ... and one that assigns all of `self`.
#include <stdlib::{core, vec}>
struct A { name: long }
struct Tok { attrs: Vec<A>, kind: long }
struct T { cur: Tok, errors: long }
methods T {
    wipe &self -> void { self = T { cur: Tok { attrs: vec![], kind: 0 }, errors: 0 }; }
    check &self -> long {
        n: long = 0;
        for a in self.cur.attrs { self.wipe(); n = n + a.name; }
        return n;
    }
}
main -> int { t: T = T { cur: Tok { attrs: vec![], kind: 0 }, errors: 0 }; return t.check() as int; }
