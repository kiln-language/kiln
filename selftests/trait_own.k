// A file's own trait (declared without `pub`) is not the standard library's of the same spelling:
// `methods long for Ord` here and in stdlib::cmp are two implementations of two traits, and this
// file's calls reach its own while the library's sort reaches the library's. A trait may also be
// declared below its implementations, and two files' traits share a method name on one type.
#include <stdlib::{cmp, sort, vec}>
trait Ord { cmp &self other:Self -> int; }
methods long for Ord {
    cmp &self other:long -> int { if (self < other) { return 1; } if (self > other) { return -1; } return 0; }
}
struct Ver { a: long }
methods Ver for Ord { cmp &self other:Ver -> int { return 7; } }
methods Ver for Shown { show &self -> long { return self.a * 10; } }
trait Shown { show &self -> long; }
mx<T: Ord> a:T b:T -> T { if (a.cmp(b) < 0) { return b; } return a; }
viaObject s:Shown -> long { return s.show(); }
main -> int {
    v: Vec<long> = vec![3, 1, 2];
    sort(&v);
    if (v.get(0) != 1 || v.get(2) != 3) { return 1; }   // the library's Ord
    if ((5 as long).cmp(2) != -1) { return 2; }            // this file's: reversed
    if (mx(3 as long, 9 as long) != 3) { return 3; }        // this file's, through a bound
    w: Ver = Ver { a: 4 };
    u: Ver = Ver { a: 5 };
    if (w.cmp(u) != 7) { return 4; }
    if (viaObject(w) != 40) { return 5; }                  // a trait declared below, as an object
    return 0;
}
