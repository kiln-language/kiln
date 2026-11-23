#include <stdlib::{string, vec}>

// An aggregate result built where it goes: a call that is not inlined writes straight into the
// local it is assigned to, and the callee builds its value in the caller's memory. Each case is
// one where doing that would show if done wrong: the destination read for the arguments, lent to
// the call (to a callee that zeroes its result first), passed by value, reachable through a pointer
// the callee reads, a field, several returns, a call on one return path reading the local returned
// on the other, a local larger than the result, a result read while it is built, recursion, an
// owning result replacing an owning value. Every function is called through a fn
// value once, so its own body is compiled as a call and not only inlined.

struct P { a: long, b: long, c: long, d: long }

// Large enough not to be inlined anywhere.
mk n:long -> P {
    p: P = P { a: n, b: n * 2, c: n * 3, d: 0 };
    i: long = 0;
    while (i < n) { p.d = p.d + p.a * i; i = i + 1; }
    if (n > 1000) { p.c = 0; }
    return p;
}

// Reads its own result while building it.
selfRead n:long -> P {
    p: P = P { a: n, b: 0, c: 0, d: 0 };
    p.b = p.a + 1;
    p.c = p.b * p.a;
    i: long = 0;
    while (i < 3) { p.d = p.d + p.c - p.b; i = i + 1; }
    return p;
}

// Two returns of different locals.
pick n:long -> P {
    x: P = P { a: 1, b: 2, c: 3, d: n };
    y: P = P { a: x.d, b: x.c, c: x.b, d: x.a };
    i: long = 0;
    while (i < n) { y.a = y.a + 1; i = i + 1; }
    if (n % 2 == 0) { return x; }
    return y;
}

// The same local returned on two paths.
twice n:long -> P {
    p: P = mk(n);
    if (n > 5) { p.a = 100; return p; }
    p.b = -1;
    return p;
}

// Takes the destination's own value by borrow and by value.
bump q:&P -> P { r: P = P { a: q.b, b: q.a, c: q.c + 1, d: q.d }; i: long = 0; while (i < 2) { r.d = r.d + r.a; i = i + 1; } return r; }
byVal q:P -> P { q.a = q.a + 10; i: long = 0; while (i < 2) { q.d = q.d + q.b; i = i + 1; } return q; }

// `return f()`: the callee is handed this function's own result pointer.
fwd n:long -> P { return mk(n + 1); }

rec n:long -> P {
    if (n == 0) { return P { a: 0, b: 0, c: 0, d: 0 }; }
    r: P = rec(n - 1);
    r.a = r.a + n;
    r.d = r.d + r.a;
    return r;
}

struct H { p: P, tag: long }

// Zeroes its result before reading its argument: built in the caller's memory while that memory
// is also the argument, it would read zeros.
reflect q:&P -> P {
    r: P = P { a: 0, b: 0, c: 0, d: 0 };
    r.a = q.b; r.b = q.a; r.c = q.c + q.a; r.d = q.d + r.a;
    i: long = 0;
    while (i < 2) { r.d = r.d + i; i = i + 1; }
    return r;
}

// Returns a local on one path and, on the other, a call that reads that local through a borrow.
viaG n:long -> P {
    s: P = P { a: n, b: n + 1, c: 0, d: 0 };
    i: long = 0;
    while (i < n) { s.c = s.c + i; i = i + 1; }
    if (n > 5) { return s; }
    return reflect(s);
}

// Returns the first field of a larger local: building that local in the result's memory would
// write past the result.
firstOf n:long -> P {
    h: H = H { p: P { a: n, b: n, c: n, d: n }, tag: 0 };
    i: long = 0;
    while (i < n) { h.tag = h.tag + 1000; h.p.d = h.p.d + i; i = i + 1; }
    return h.p;
}

// Reads the caller's destination through a pointer it was given before the call.
var gSeen: *P = 0 as *P;
peek n:long -> P {
    r: P = P { a: 0, b: 0, c: 0, d: 0 };
    unsafe { r.a = gSeen.a + n; r.b = gSeen.a; r.c = gSeen.b; }
    i: long = 0;
    while (i < n) { r.d = r.d + r.b; i = i + 1; }
    return r;
}

name n:long -> String {
    s: String = String.new();
    i: long = 0;
    while (i < n) { s.push('a'); i = i + 1; }
    return s;
}

sum p:&P -> long { return p.a + p.b * 10 + p.c * 100 + p.d * 1000; }

main -> long {
    f1: fn(long) -> P = &mk; f2: fn(long) -> P = &selfRead; f3: fn(long) -> P = &pick;
    f4: fn(long) -> P = &twice; f5: fn(&P) -> P = &bump; f6: fn(P) -> P = &byVal;
    f7: fn(long) -> P = &fwd; f8: fn(long) -> P = &rec; f9: fn(&P) -> P = &reflect; f10: fn(long) -> P = &viaG;
    f11: fn(long) -> P = &firstOf; f12: fn(long) -> P = &peek;
    if (sum(f1(4)) != sum(mk(4)) || sum(f2(3)) != sum(selfRead(3)) || sum(f3(3)) != sum(pick(3))
        || sum(f4(7)) != sum(twice(7)) || sum(f7(2)) != sum(fwd(2)) || sum(f8(4)) != sum(rec(4))) { return 1; }

    x: P = mk(4);
    if (x.a != 4 || x.b != 8 || x.c != 12 || x.d != 24) { return 2; }
    x = mk(x.a + x.b);                       // the destination read for the argument
    if (x.a != 12 || x.d != 792) { return 3; }
    x = bump(x);                             // lent to the call
    if (x.a != 24 || x.b != 12 || x.c != 37 || x.d != 840) { return 4; }
    x = byVal(x);                            // passed by value
    if (x.a != 34 || x.d != 864) { return 5; }
    y: P = selfRead(5);
    if (y.b != 6 || y.c != 30 || y.d != 72) { return 6; }
    z: P = pick(4);
    w: P = pick(3);
    if (z.d != 4 || w.a != 6 || w.d != 1) { return 7; }
    t1: P = twice(7);
    t2: P = twice(2);
    if (t1.a != 100 || t2.b != -1 || t2.a != 2) { return 8; }
    v: P = fwd(2);
    if (v.a != 3 || v.d != 9) { return 9; }
    r: P = rec(4);
    if (r.a != 10 || r.d != 20) { return 10; }
    h: H = H { p: P { a: 0, b: 0, c: 0, d: 0 }, tag: 77 };
    h.p = mk(3);                             // a field at the start of its struct
    if (h.p.d != 9 || h.tag != 77) { return 11; }
    s: String = name(3);
    s = name(5);                             // an owning value replaced: the old one released
    if (s.len() != 5) { return 12; }
    ps: Vec<P> = vec![];
    for k in 0..4 { ps.push(mk(k)); }
    if (ps[3].d != 9 || ps[2].b != 4) { return 13; }
    rf: P = mk(3);
    rf = reflect(rf);                        // lent to a callee that zeroes its result first
    if (rf.a != 6 || rf.b != 3 || rf.c != 12 || rf.d != 16) { return 14; }
    rl: P = mk(3);                           // the same, lent and never exposed
    rl = reflect(rl);
    if (rl.a != 6 || rl.b != 3 || rl.c != 12 || rl.d != 16) { return 19; }
    g1: P = viaG(3);
    g2: P = viaG(7);
    if (g1.a != 4 || g1.b != 3 || g1.c != 6 || g1.d != 5 || g2.a != 7 || g2.c != 21) { return 15; }
    wh: H = H { p: P { a: 0, b: 0, c: 0, d: 0 }, tag: 77 };
    wh.p = firstOf(3);                       // a callee whose local is larger than its result
    if (wh.tag != 77 || wh.p.d != 6 || wh.p.a != 3) { return 16; }
    pk: P = mk(2);
    unsafe { gSeen = &pk as *P; }
    pk = peek(5);                            // the destination's address is out
    if (pk.a != 7 || pk.b != 2 || pk.c != 4 || pk.d != 10) { return 17; }
    if (sum(f9(rf)) != sum(reflect(rf)) || sum(f10(4)) != sum(viaG(4)) || sum(f11(2)) != sum(firstOf(2))
        || sum(f12(1)) != sum(peek(1))) { return 18; }
    return 0;
}
