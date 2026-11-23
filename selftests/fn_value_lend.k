// Through a fn value whose type lends a struct or a slice, the callee cannot write it (batch 9):
// the function held must fit the type, an `inout` callee is no fn value, and a slice is written
// only through `inout`. So an immutable global struct or array may be lent through one, and a
// `for` over a collection may hand it to one. (Both were refused: "is passed through a function
// value, whose callee cannot be checked", "handed to ..., which writes it".)
#include <stdlib::{io, vec}>
struct P { x: long, y: long }
G: P = P { x: 3, y: 4 };
A: [long; 3] = [1, 2, 3];
sumP p:P -> long { return p.x + p.y; }
bumpP p:P -> long { p.x = p.x + 100; return p.x; }          // writes its own copy
total xs:[long] -> long { t: long = 0; for x in xs { t = t + x; } return t; }
count v:&Vec<long> -> long { return v.len(); }
main -> int {
    f: fn(P)->long = &sumP;
    g: fn(sink P)->long = &bumpP;
    h: fn([long])->long = &total;
    if (f(G) != 7) { return 1; }
    if (g(G) != 103 || G.x != 3) { return 2; }
    if (h(A[..]) != 6) { return 3; }
    xs: Vec<long>; xs.push(5); xs.push(6);
    c: fn(Vec<long>)->long = &count;
    t: long = 0;
    for x in xs { t = t + x * c(xs); }
    if (t != 22) { return 4; }
    return 0;
}
