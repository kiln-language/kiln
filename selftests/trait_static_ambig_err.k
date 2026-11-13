// `P.new()` where two traits give P a `new`: ambiguous, and the message says how to name one.
pub trait Fresh { new -> Self; }
struct P { a: long }
methods P for Fresh { new -> P { return P { a: 5 }; } }
methods P for Default { new -> P { return P { a: 7 }; } }
main -> long { p: P = P.new(); return p.a; }
