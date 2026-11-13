// `&` at a call site: lends to an `inout` parameter (required from a local), and is accepted, as
// the borrow passing already is, for a parameter that only reads (`r:&P`, or one inferred a
// read); an `inout` parameter is forwarded with or without it. So one call reads the same in a
// function that owns the value and in one that was lent it.
struct P { x: long }
bump inout p:P -> void { p.x = p.x + 1; }
look r:&P -> long { return r.x; }
peek r:P -> long { return r.x; }
fwd inout q:P -> long { bump(&q); bump(q); return look(&q) + peek(&q) + look(q); }
main -> int {
    p: P = P { x: 1 };
    s: long = fwd(&p);                          // p.x = 3; 3 + 3 + 3
    s = s + look(&p) + peek(&p) + look(p);      // 9 more
    return (s + p.x) as int;                    // 21
}
