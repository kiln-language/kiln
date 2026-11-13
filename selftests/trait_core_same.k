// A trait of the program's own sharing a method name with a core trait, implemented for one type
// in either order (and for a type that implements only one of them): the core trait's
// implementation keeps the plain name the compiler calls (`P_new`, `P_display`), the other
// carries its trait's (`P_Fresh_new`), decided from the core traits alone. (Both used to be
// `P_new` when the program's trait came first: "'P.new' is defined twice".)
pub trait Fresh { new -> Self; }
pub trait Shown { display &self -> long; }
struct P { a: long }
methods P for Fresh { new -> P { return P { a: 5 }; } }
methods P for Default { new -> P { return P { a: 7 }; } }
methods P for Shown { display &self -> long { return self.a + 100; } }
methods P for Display { display &self w:Write -> void { } }
struct Q { a: long }
methods Q for Default { new -> Q { return Q { a: 1 }; } }
methods Q for Fresh { new -> Q { return Q { a: 2 }; } }
struct R { a: long }
methods R for Fresh { new -> R { return R { a: 9 }; } }
methods R for Shown { display &self -> long { return self.a; } }
struct H { p: P, q: Q }
main -> long {
    f: P = P { a: 5 };
    if (Shown.display(f) != 105) { return 2; }
    r: R = R.new();
    if (r.a != 9 || r.display() != 9) { return 4; }
    h: H = H { };                      // omitted fields: each type's Default
    if (h.p.a != 7 || h.q.a != 1) { return 5; }
    return 42;
}
