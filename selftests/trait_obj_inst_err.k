// An object of one instantiation of a parameterized trait is not made from a type that
// implements only another.
struct P { a: long }
pub trait Scale<T> { scale &self t:T -> long; }
struct K { k: long }
methods K for Scale<long> { scale &self t:long -> long { return self.k * t; } }
use s:Scale<P> -> long { return s.scale(P { a: 1 }); }
main -> long { kk: K = K { k: 2 }; return use(kk); }
