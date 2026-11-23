#include <stdlib::iter>

// A value handed straight to a parameter typed as an instance of a parameterized trait
// (`Iter<long>`, `Scale<P>`): the instance is implemented under its base trait with arguments.
struct P { a: long, b: long }
trait Scale<T> { scale &self t:T -> long; }
pub trait Pick<T> { pick &self t:T -> long; }
struct K { k: long }
methods K for Scale<P> { scale &self t:P -> long { return self.k * (t.a + t.b); } }
methods K for Scale<long> { scale &self t:long -> long { return self.k * t; } }
methods K for Pick<P> { pick &self t:P -> long { return t.b - t.a; } }

sumIt it:Iter<long> -> long { t: long = 0; while (it.hasNext()) { t = t + it.next(); } return t; }
scaledP s:Scale<P> p:P -> long { return s.scale(p); }
scaledL s:Scale<long> n:long -> long { return s.scale(n); }
picked s:Pick<P> p:P -> long { return s.pick(p); }

main -> long {
    if (sumIt(range(0, 5)) != 10) { return 1; }
    kk: K = K { k: 2 };
    p: P = P { a: 3, b: 7 };
    if (scaledP(kk, p) != 20) { return 2; }
    if (scaledL(kk, 4) != 8) { return 3; }
    if (picked(kk, p) != 4) { return 4; }
    return 0;
}
