// A trait method may lend a parameter `inout`, written before the name as a function writes it or
// after the colon as a fn type does; an implementation says the same, and a call through the trait
// object lends with `&`. 4 + 2 + 3 = 9.
#include <stdlib::vec>
trait Fill { fill &self inout v:Vec<long> -> void; more &self v:inout Vec<long> -> void; }
struct S { a: long }
methods S for Fill {
    fill &self inout v:Vec<long> -> void { v.push(self.a); }
    more &self inout v:Vec<long> -> void { v.push(self.a); v.push(self.a); }
}
viaObject f:Fill inout v:Vec<long> -> void { f.fill(v); f.more(v); }
main -> int {
    s: S = S { a: 4 };
    v: Vec<long>;
    s.fill(&v);
    viaObject(s, &v);
    return (v.get(0) + v.len() - 1 + v.len() - 2 + 3 - 3 + 0) as int;
}
