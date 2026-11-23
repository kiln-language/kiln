// A fixed array is a value: assigning one, declaring one from another, putting one in a struct
// literal's array field copies every element. Until batch 8 each of these stored the source's
// address into the destination's first element (`b = a`, `b: [long; 3] = a`, `S { v: a }`), a
// struct element's copy moved one element's bytes, the evaluator read the first element as the
// array's address, and the derived `clone` of a struct with an array field copied the address.
// Each form below is checked against values the optimizer cannot see, then the source is changed
// to show the copy is not an alias. Element widths 1, 4 and 8, and a struct element.
#include <stdlib::fixedstring>

var gV: long = 0;
dyn v:long -> long { gV = v; return gV; }

struct P { x: long, y: long }
struct S { v: [long; 3], n: long }
struct Inner { v: [long; 3] }
struct Outer { k: long, in: Inner }
struct H { d: [u8; 4], n: long }

G1: [long; 3] = [4, 5, 6];
G2: [long; 3] = G1;                       // folded by the evaluator
var gG3: [long; 3] = G1;                  // a `var` global's initializer

// Compile time: the evaluator copies too.
folded -> long {
    a: [long; 3] = [1, 2, 3];
    b: [long; 3] = a;
    a[1] = 9;
    c: [long; 3];
    c = b;
    s: S = S { v: c, n: 0 };
    return s.v[0] * 100 + s.v[1] * 10 + s.v[2];
}
FOLDED: long = folded();

sum3 a:[long] -> long { return a[0] * 100 + a[1] * 10 + a[2]; }

main -> int {
    bad: long = 0;
    x: long = dyn(1);
    a: [long; 3] = [x, x + 1, x + 2];
    // A declaration from an array.
    b: [long; 3] = a;
    a[1] = 50;
    if (sum3(b[..]) != 123) { bad = bad | 1; }
    // An assignment.
    c: [long; 3];
    c = b;
    b[0] = 7;
    if (sum3(c[..]) != 123) { bad = bad | 2; }
    // A struct literal's array field, then a field to a local and a local to a nested field.
    s: S = S { v: c, n: 4 };
    c[2] = 0;
    if (sum3(s.v[..]) != 123 || s.n != 4) { bad = bad | 4; }
    d: [long; 3] = s.v;
    o: Outer = Outer { k: 1, in: Inner { v: [0, 0, 0] } };
    o.in.v = d;
    s.v[0] = 9;
    if (sum3(o.in.v[..]) != 123 || o.k != 1) { bad = bad | 8; }
    // Field to field.
    t: S = S { v: [0, 0, 0], n: 5 };
    t.v = o.in.v;
    if (sum3(t.v[..]) != 123 || t.n != 5) { bad = bad | 16; }
    // Assigned to itself.
    t.v = t.v;
    if (sum3(t.v[..]) != 123) { bad = bad | 16; }
    // Narrow elements and struct elements: the stride is the element's.
    u: [u8; 5] = [dyn(1) as u8, 2, 3, 4, 5];
    w: [u8; 5] = u;
    u[4] = 0;
    if (w[0] != 1 || w[4] != 5) { bad = bad | 32; }
    i4: [int; 3] = [dyn(7) as int, 8, 9];
    j4: [int; 3];
    j4 = i4;
    if (j4[0] != 7 || j4[2] != 9) { bad = bad | 32; }
    ps: [P; 2] = [P { x: dyn(1), y: 2 }, P { x: 3, y: 4 }];
    qs: [P; 2] = ps;
    ps[1].y = 0;
    if (qs[0].x != 1 || qs[1].y != 4) { bad = bad | 64; }
    // Globals: folded, and run at startup.
    if (sum3(G2[..]) != 456 || sum3(gG3[..]) != 456) { bad = bad | 128; }
    if (FOLDED != 123) { bad = bad | 256; }
    // The derived clone of a struct with an array field.
    h: H = H { d: [dyn(1) as u8, 2, 3, 4], n: 9 };
    h2: H = h.clone();
    if (h2.d[0] != 1 || h2.d[3] != 4 || h2.n != 9) { bad = bad | 512; }
    fs: FixedString<16> = fixedOf("hello");
    fs2: FixedString<16> = fs.clone();
    if (fs2 != "hello") { bad = bad | 1024; }
    return (bad != 0) as int;
}
