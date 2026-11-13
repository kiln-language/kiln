// ... and so is one that reaches it by lending `self.cur` onward to a function that writes it.
#include <stdlib::{core, vec}>
struct A { name: long }
struct Tok { attrs: Vec<A>, kind: long }
struct T { cur: Tok, errors: long }
reset inout t:Tok -> void { t.attrs.clear(); }
methods T {
    zap &self -> void { reset(&self.cur); }
    check &self -> long {
        n: long = 0;
        for a in self.cur.attrs { self.zap(); n = n + a.name; }
        return n;
    }
}
main -> int { t: T = T { cur: Tok { attrs: vec![], kind: 0 }, errors: 0 }; return t.check() as int; }
