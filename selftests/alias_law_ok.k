// What the law of exclusivity still allows through a borrowed binding, built with the optimizer on
// (as every selftest is): the binding lent beside a disjoint field of the same value, and the value
// read after the call. The callee writes through the binding and reads the other field, and the
// caller sees the write. Exits with the number of the first check that fails.
struct P { x: long, y: long }
enum E { Num(long), Pt(P) }
struct H { e: E, q: P, n: long }
// Writes through `p`, reads `q` (a part of the same `H`, but not the part `p` is), reads `p` again.
mix inout p:P q:&P -> long {
    before: long = p.x;
    p.x = p.x + q.x;
    return before * 1000 + p.x;
}
xOf e:&E -> long { match e { Pt(p) { return p.x; } _ { } } return -1; }
run inout h:H -> long { match h.e { Pt(p) { return mix(&p, h.q); } _ { } } return 0; }
main -> int {
    h: H = H { e: E.Pt(P { x: 1, y: 2 }), q: P { x: 40, y: 0 }, n: 0 };
    if (run(&h) != 1041) { return 1; }
    if (xOf(h.e) != 41) { return 2; }
    if (run(&h) != 41081) { return 3; }
    return 0;
}
