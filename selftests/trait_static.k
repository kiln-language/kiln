// A static method two traits give one type is named by its trait, for the type its result goes
// to: `p: P = Fresh.new();` is Fresh's, `Default.new()` the core trait's, as `Shown.display(p)`
// names a method. The destination may be a declaration, an assignment, a parameter or a return.
pub trait Fresh { new -> Self; }
pub trait Make { make n:long -> Self; }
struct P { a: long }
methods P for Fresh { new -> P { return P { a: 5 }; } }
methods P for Default { new -> P { return P { a: 7 }; } }
methods P for Make { make n:long -> P { return P { a: n }; } }
struct Q { a: long }
methods Q for Make { make n:long -> Q { return Q { a: n * 2 }; } }
methods Q for Fresh { new -> Q { return Q { a: 3 }; } }
fresh -> P { return Fresh.new(); }
take p:P -> long { return p.a; }
main -> long {
    p: P = Fresh.new();
    d: P = Default.new();
    if (p.a != 5 || d.a != 7) { return 1; }
    if (fresh().a != 5 || take(Default.new()) != 7) { return 2; }
    q: Q = Make.make(4);
    m: P = Make.make(9);
    if (q.a != 8 || m.a != 9) { return 3; }
    q = Fresh.new();
    if (q.a != 3) { return 4; }
    return 42;
}
