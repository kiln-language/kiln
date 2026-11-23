// A borrowed parameter's own bytes change during the call only through that parameter, so what
// was read of them survives a store to a `var` global by name, a store through another borrowed
// parameter, and a call that is not handed the parameter, and is read again after a call that is
// handed it to write. A local lent to a call through a fn value whose type lends it (`fn(Acc)`, not
// `fn(&Acc)`, through which the callee may write), or to a recursive function, is not changed by
// it where the parameter only reads.
// ir-count: borrows::afterGlobal ptrload 1
// ir-count: borrows::otherParam ptrload 1
// ir-count: borrows::afterCall ptrload 1
// ir-count: borrows::lentWrite ptrload 2
// ir-lacks: borrows::viaFnValue ptrload
// ir-lacks: borrows::viaRecursion ptrload
struct Acc { n: long, total: long }
var gCount: long = 0;
var gSink: long = 0;

afterGlobal r:&Acc -> long { x: long = r.n; gCount = gCount + 1; return x + r.n; }
otherParam inout a:Acc b:&Acc -> long { x: long = b.n; a.n = 7; return x + b.n; }

// Big enough, and called from two places, to stay a call; it writes a global and nothing it is
// handed.
noise k:long -> void {
    s: long = 0;
    for i in 0..k { s = s + i * 3; s = s ^ (s >> 2); s = s + (i & 5); s = s - (s >> 3); }
    for i in 0..k { s = s + i * 7; s = s ^ (s >> 1); s = s + (i | 9); s = s - (s >> 4); }
    gSink = gSink + s;
}
afterCall r:&Acc -> long { x: long = r.n; noise(3); return x + r.n; }

// Writes what it is lent, and stays a call for the same reasons.
scramble inout a:Acc k:long -> void {
    s: long = 0;
    for i in 0..k { s = s + i * 3; s = s ^ (s >> 2); s = s + (i & 5); s = s - (s >> 3); }
    for i in 0..k { s = s + i * 7; s = s ^ (s >> 1); s = s + (i | 9); s = s - (s >> 4); }
    a.n = a.n + s + 1;
}
lentWrite inout a:Acc -> long { x: long = a.n; scramble(&a, 2); return x + a.n; }

look p:Acc -> long { return p.n * 2; }
viaFnValue f:fn(Acc)->long -> long {
    q: Acc = Acc { n: 5, total: 6 };
    a: long = f(q);
    return a + q.total;
}
depth p:&Acc n:long -> long {
    if (n == 0) { return p.n; }
    return depth(p, n - 1) + 1;
}
viaRecursion -> long {
    q: Acc = Acc { n: 3, total: 4 };
    a: long = depth(q, 5);
    return a + q.total;
}

main -> int {
    c: Acc = Acc { n: 2, total: 0 };
    d: Acc = Acc { n: 9, total: 0 };
    if (afterGlobal(c) != 4) { return 1; }
    if (otherParam(&c, d) != 18 || c.n != 7) { return 2; }
    if (afterCall(d) != 18) { return 3; }
    noise(4);
    if (lentWrite(&c) <= 14) { return 4; }
    scramble(&d, 1);
    if (viaFnValue(&look) != 16) { return 5; }
    if (viaRecursion() != 12) { return 6; }
    return 0;
}
