// A struct literal's array field takes an array literal naming every element: scalars, a
// computed value, structs, owning values (each moved in and released once with the struct), in
// a body, nested, returned, and in a global the evaluator folds.
#include <stdlib::{string, vec}>
struct Pt { x: long, y: long }
struct S { xs: [long; 3], n: long }
struct T { ps: [Pt; 2], tag: u8 }
struct O { names: [String; 2] }
struct W { inner: S, bytes: [u8; 5] }
G: S = S { xs: [10, 20, 30], n: 4 };
make k:long -> S { return S { xs: [k, k + 1, k * 2], n: 0 }; }
main -> long {
    s: S = S { xs: [1, 2, 3], n: 4 };
    if (s.xs[0] + s.xs[1] + s.xs[2] + s.n != 10) { return 1; }
    t: T = T { ps: [Pt { x: 1, y: 2 }, Pt { x: 3, y: 4 }], tag: 9 };
    if (t.ps[1].y != 4 || t.tag != 9) { return 2; }
    a: String = stringOf("ab");
    o: O = O { names: [a, stringOf("cde")] };
    if (o.names[0].len() + o.names[1].len() != 5) { return 3; }
    w: W = W { inner: make(5), bytes: [1, 2, 3, 4, 5] };
    if (w.inner.xs[2] != 10 || w.bytes[4] != 5) { return 4; }
    if (G.xs[1] != 20 || G.n != 4) { return 5; }
    return 42;
}
