// The shapes the inliner and the dataflow rewrite, each computing the right thing:
//   * a callee's early return tested in its caller (`if (n <= c.cap) { return; }`), both ways;
//   * a function called once, with an aggregate local of its own, copied into a loop (its local
//     renamed, so it is not the caller's `p`), and one called once that is recursive;
//   * the same local name in two copies of one body, both live at once;
//   * an expression computed again after an operand changed, on one path and on both;
//   * a struct whose address escapes to a callee: its stores are read there, and stay.
struct Counter { cap: long, grows: long }
struct P { a: long, b: long }

grow inout c:Counter n:long -> void {
    if (n <= c.cap) { return; }
    c.cap = n;
    c.grows = c.grows + 1;
}

// Called once; holds a struct local named like the caller's.
mix x:long -> long {
    p: P = P { a: x * 3, b: x + 7 };
    q: P = P { a: p.b, b: p.a };
    return q.a * 10 + q.b;
}

// Called once, and calls itself.
depth n:long -> long { if (n == 0) { return 0; } return 1 + depth(n - 1); }

pair x:long -> P { p: P = P { a: x, b: x * x }; return p; }

sum2 p:P -> long { return p.a + p.b; }
var gEsc: long = 0;
look p:&P -> void { gEsc = p.a * 100 + p.b; }

reuse a:long b:long flag:bool -> long {
    x: long = a * b;
    if (flag) { a = a + 1; }
    y: long = a * b;          // a changed on one path: not x
    a = a + 1;
    z: long = a * b;          // changed on every path
    return x * 10000 + y * 100 + z;
}

main -> int {
    bad: long = 0;
    c: Counter = Counter { cap: 4, grows: 0 };
    for i in 0..10 { grow(&c, i); }
    grow(&c, 3);
    if (c.cap != 9 || c.grows != 5) { bad = bad | 1; }

    p: P = P { a: 1, b: 2 };
    t: long = 0;
    for i in 0..5 { t = t + mix(i); }
    if (t != 480 || p.a != 1 || p.b != 2) { bad = bad | 2; }
    if (depth(50) != 50) { bad = bad | 4; }

    s: long = sum2(pair(3)) + sum2(pair(4));
    u: P = pair(5);
    v: P = pair(6);
    if (s != 32 || u.a + v.a != 11 || u.b + v.b != 61) { bad = bad | 8; }

    if (reuse(3, 5, true) != 152025 || reuse(3, 5, false) != 151520) { bad = bad | 16; }

    e: P = P { a: 7, b: 8 };
    look(&e);
    if (gEsc != 708) { bad = bad | 32; }
    return bad as int;
}
