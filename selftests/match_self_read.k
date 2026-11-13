// In a match arm that holds a borrow of the payload, a `&self` method that only reads `self`
// (a clone, a length) is a read-only lend and is accepted; one that writes `self` is refused
// (match_borrow_write_err). Every release counted.
#include <stdlib::string>
var gDrops: long = 0;
struct Res { n: long }
methods Res for Drop { drop &self -> void { gDrops = gDrops + 1; } }
methods Res for Clone { clone &self -> Res { return Res { n: self.n }; } }
enum Expr { Num(long), Name(String), Held(Res) }
methods Expr for Clone {
    clone &self -> Expr {
        match self { Num(n) { return Expr.Num(n); } Name(s) { return Expr.Name(s.clone()); } Held(r) { return Expr.Held(r.clone()); } }
    }
}
methods Expr { weight &self -> long { match self { Num(n) { return n; } Name(s) { return s.len; } Held(r) { return r.n; } } } }
f e:&Expr -> long {
    match e {
        Num(n) { c: Expr = e.clone(); return n + c.weight(); }
        Name(s) { c: Expr = e.clone(); return s.len + c.weight() + e.weight(); }
        Held(r) { return r.n + e.weight(); }
    }
}
main -> int {
    a: Expr = Expr.Name(stringOf("abc"));
    b: Expr = Expr.Num(4);
    c: Expr = Expr.Held(Res { n: 5 });
    t: long = f(a) + f(b) + f(c);             // 9 + 8 + 10
    if (t != 27) { return 1; }
    return 0;
}
