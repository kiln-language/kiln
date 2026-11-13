// `for x in xs` over a generic slice `[T]`: the element is the type parameter, substituted per
// instance (at T = str it stayed T: "'x' is a T, and this gives it a str"). At str, long and a
// struct: 2 + 3 + 2 + ('q' = 113) + 3 = 123.
#include <stdlib::vec>
struct P { a: long, b: long }
pushAll<T> inout v:Vec<T> xs:[T] -> void { for x in xs { v.push(x); } }
countAll<T> xs:[T] -> long { n: long = 0; for x in xs { n = n + 1; } return n; }
main -> int {
    v: Vec<str>;
    a: [str; 2] = ["p", "q"];
    pushAll(&v, a[..]);
    w: Vec<long>;
    b: [long; 3] = [1, 2, 3];
    pushAll(&w, b[..]);
    ps: [P; 2] = [P { a: 1, b: 2 }, P { a: 3, b: 4 }];
    s: str = v[1];
    return (v.len() + w.len() + countAll(ps[..]) + (s[0] as long) + w[2]) as int;
}
