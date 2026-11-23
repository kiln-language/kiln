#include <stdlib::io>
#include <stdlib::string>

// A closure over a struct parameter, held as a trait object. The trait instance is spelled with
// its arguments (`Fn1_closure_struct_obj::P_long`), and the module qualifier in that spelling
// once made the table name a method that was never emitted.

struct P { a: long, b: long }

// A trait this module owns, instantiated over a struct: its methods carry the trait's name.
trait Scale<T> { scale &self t:T -> long; }
struct K { k: long }
methods K for Scale<P> { scale &self t:P -> long { return self.k * (t.a + t.b); } }

viaRef f:Fn(&P) -> long p:P -> long { return f(p) + f(p); }
viaTwo f:Fn(P, &P) -> long p:P q:P -> long { return f(p, q); }
viaStr f:Fn(&String) -> long s:String -> long { return f(s); }
viaBound<F: Fn(P) -> long> f:F p:P -> long { return f(p); }
scaled s:Scale<P> p:P -> long { return s.scale(p); }

main -> long {
    k: long = 3;
    p: P = P { a: 1, b: 2 };
    q: P = P { a: 10, b: 20 };
    f: Fn(P) -> long = |x: P| x.a + x.b + k;
    if (f(p) != 6) { return 1; }
    if (viaRef(|x: &P| x.a * x.b, q) != 400) { return 2; }
    if (viaTwo(|x: P, y: &P| x.a + y.b + k, p, q) != 24) { return 3; }
    s: String = String.new();
    s.pushStr("hello");
    if (viaStr(|t: &String| t.len() + k, s) != 8) { return 4; }
    if (viaBound(|x: P| x.b - x.a, q) != 10) { return 5; }
    seen: long = 0;
    g: Fn(&P) -> void = |x: &P| { seen = seen + x.a; };
    g(p); g(q);
    if (seen != 11) { return 6; }
    kk: K = K { k: 2 };
    if (scaled(kk, q) != 60) { return 7; }
    return 0;
}
