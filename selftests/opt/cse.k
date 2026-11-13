// The same expression computed twice is computed once: `v.get(i) * v.get(i)` shifts `i` once,
// adds it to the buffer once and loads the element once.
// ir-count: cse::sq shl 1
// A struct built only to be read back leaves no store behind: its fields are forwarded to the
// reads and the scratch it was built in, and the local it was copied to, are never written.
// ir-lacks: cse::area ptrstore
// ir-lacks: cse::area aggcopy
#include <stdlib::vec>
struct P { a: long, b: long }
mk x:long -> P { return P { a: x, b: x + 1 }; }
sq v:Vec<long> -> long { s: long = 0; for i in 0..v.len() { s = s + v.get(i) * v.get(i); } return s; }
area x:long -> long { p: P = mk(x); return p.a * p.b; }
main -> int {
    v: Vec<long>;
    for i in 0..10 { v.push(i); }
    if (sq(v) != 285 || area(6) != 42) { return 1; }
    return 0;
}
