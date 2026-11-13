// What a bound held at the call must still let through: a closure and a fn value against an `Fn`
// bound, a struct whose `Eq` is derived on demand, a scalar with an implementation, a derived
// clone, and a type a derive gives the trait (`Encode`). 7 + 9 + 1 + 3 + 5 + 1 = 26.
#include <stdlib::{vec, encode, cmp}>
apply<F: Fn(long) -> long> f:F x:long -> long { return f(x); }
twice x:long -> long { return x * 2 + 1; }
same<T: Eq<T>> a:T b:T -> bool { return a == b; }
struct P { x: long, y: long }
big<T: Ord> a:T b:T -> T { if (a.cmp(b) < 0) { return b; } return a; }
dup<T: Clone> v:T -> T { return v.clone(); }
struct Q { n: long }
size<T: Encode> v:T -> long { e: Encoder = Encoder.new(); v.encode(e); return e.len(); }
main -> int {
    k: long = 3;
    t: long = apply(|v: long| v + 4, k) + apply(&twice, 4);
    if (same(P { x: 1, y: 2 }, P { x: 1, y: 2 })) { t = t + 1; }
    t = t + big(3 as long, 2 as long);
    t = t + dup(5 as long);
    t = t + size(Q { n: 7 });
    return t as int;
}
