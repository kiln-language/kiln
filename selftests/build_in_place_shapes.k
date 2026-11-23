#include <stdlib::{io, result, vec}>

// A value built where it is copied to (`flow.k` `buildWhereCopied`) must still see the old value
// wherever the source says it does: a literal reading what it replaces, a call in it handed the
// destination, a `?` leaving in the middle of one with the old value still to release, a loop of
// them, two values swapped through literals, and a value returned through an inlined callee.
// Every release is counted, so a double release or a leak changes the sums.

var gDrops: long = 0;
struct Res { id: long }
methods Res for Drop { drop &self -> void { gDrops = gDrops + self.id; } }
struct Holder { r: Res, n: long, items: Vec<long> }
struct Pair { a: long, b: long, c: long, d: long }

look h:&Holder -> long { return h.n * 100 + h.items.len(); }
check n:long -> Result<long, long> { if (n > 2) { return Result.Err(n); } return Result.Ok(n); }

// the literal reads what it replaces, directly and through a call
selfRead -> long {
    h: Holder = Holder { r: Res { id: 1 }, n: 2, items: vec![5] };
    h = Holder { r: Res { id: 10 }, n: h.n + look(&h), items: vec![h.n, h.n] };
    return h.n * 10 + h.items.len();                      // (2 + 201) * 10 + 2
}

// a `?` in the literal: the old value is released once, by the scope, and the new one is never
// built
replaceOrLeave k:long -> Result<long, long> {
    h: Holder = Holder { r: Res { id: 100 }, n: 1, items: vec![] };
    h = Holder { n: check(k)?, r: Res { id: 1000 }, items: vec![k] };
    return Result.Ok(h.n);
}

// built again on every trip
loopBuilt -> long {
    h: Holder = Holder { r: Res { id: 0 }, n: 0, items: vec![] };
    for i in 1..4 { h = Holder { r: Res { id: i * 10000 }, n: i, items: vec![i, i] }; }
    return h.n;
}

// two Copy values swapped through literals
swapped -> long {
    x: Pair = Pair { a: 1, b: 2, c: 3, d: 4 };
    y: Pair = Pair { a: 5, b: 6, c: 7, d: 8 };
    t: Pair = Pair { a: x.a, b: x.b, c: x.c, d: x.d };
    x = Pair { a: y.a, b: y.b, c: y.c, d: y.d };
    y = Pair { a: t.d, b: t.c, c: t.b, d: t.a };
    return x.a * 1000 + y.a * 100 + x.d * 10 + y.d;        // 5, 4, 8, 1
}

// a callee's local returned and inlined into a caller that then lends it
grown n:long -> Holder {
    h: Holder = Holder { r: Res { id: 1000000 }, n: n, items: vec![] };
    h.items.push(n);
    return h;
}
viaCallee n:long -> long { h: Holder = grown(n); return look(&h); }

main -> int {
    if (selfRead() != 2032) { return 1; }
    if (gDrops != 11) { return 2; }
    r: Result<long, long> = replaceOrLeave(1);
    if (r.unwrapOr(-1) != 1 || gDrops != 1111) { return 3; }
    q: Result<long, long> = replaceOrLeave(7);
    if (q.unwrapOr(-1) != -1 || gDrops != 1211) { return 4; }
    if (loopBuilt() != 3 || gDrops != 61211) { return 5; }
    if (swapped() != 5481) { return 6; }
    if (viaCallee(9) != 901 || gDrops != 1061211) { return 7; }
    println("build_in_place_shapes");
    return 0;
}
