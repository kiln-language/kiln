// `flow.k`'s `forwardCopies`: `copy A <- B` then `copy C <- A` becomes `copy C <- B` when nothing
// between writes A or B. Each function below builds a struct, copies it on, and writes one side
// or the other in between, in the ways that must stop the forwarding: a store into the copy, a
// store into its source, a call the source is lent to, a loop that writes the source after the
// copy and comes back; and copies of other bytes of the slot than the first copy wrote. The answers are checked against the arithmetic, on values the
// optimizer cannot see.

var gV: long = 0;
dyn v:long -> long { gV = v; return gV; }

struct Pair { x: long, y: long, z: long }

mk n:long -> Pair { return Pair { x: n, y: n * 2, z: n + 5 }; }

// A chain with nothing in between: forwarded, and the same value.
chain n:long -> Pair { a: Pair = mk(n); b: Pair = a; return b; }

// The copy is written before it is copied on: the last copy reads the copy.
intoCopy n:long -> Pair { a: Pair = mk(n); a.x = 7; return a; }

// The source is written after the copy: the copy keeps the old value.
intoSource n:long -> Pair {
    t: Pair = mk(n);
    t.y = 3;
    a: Pair = t;
    t.x = 9;
    return a;
}

// A call the source is lent to writes it after the copy (called from two places and too large
// to inline, so it stays a call that keeps no pointer, and nothing between the call and the last
// copy starts a block).
bump inout t:Pair k:long -> void {
    s: long = 0;
    for i in 0..k { s = s + i * gV; if (s > 1000000) { s = s % 7; } if (s < -1000000) { s = s % 5; } }
    if (s == -1) { t.y = 0; t.z = 0; }
    t.x = t.x + 100;
}
throughCall n:long -> Pair {
    t: Pair = mk(n);
    t.y = 4;
    a: Pair = t;
    bump(&t, dyn(1));
    return a;
}

// A loop copies the source and then writes it, and comes back to the copy of the copy: a label
// ends what the walk knows (`a` is the source one trip behind).
keep inout p:Pair k:long -> long { if (k > 0) { return keep(p, k - 1); } return p.x * 1000 + p.y; }
looped n:long -> long {
    t: Pair = mk(n);
    t.z = 1;
    a: Pair = t;
    acc: long = 0;
    for i in 0..dyn(3) {
        b: Pair = a;
        acc = acc + keep(&b, 0);
        a = t;
        t.x = t.x + 1;
    }
    return acc;
}

// A smaller copy into the head of a larger slot: copying the whole slot on reads more than that
// copy wrote, so it reads the slot.
struct Outer { p: Pair, w: long }
wider n:long -> Outer {
    o: Outer = Outer { p: Pair { x: 0, y: 0, z: 0 }, w: dyn(n + 40) };
    o.p = mk(n);
    q: Outer = o;
    return q;
}

// A copy into one field and a copy out of another: different bytes of one slot.
struct Two { a: Pair, b: Pair }
fieldOff n:long -> Pair {
    o: Two = Two { a: Pair { x: dyn(n + 1), y: 6, z: 8 }, b: Pair { x: 0, y: 0, z: 0 } };
    o.b = mk(n);
    r: Pair = o.a;
    return r;
}

// Each is called through a function value, so its own body is what runs (called once directly,
// it would be inlined into `main` and its shapes changed there).
main -> int {
    fChain: fn(long) -> Pair = &chain;
    fIntoCopy: fn(long) -> Pair = &intoCopy;
    fIntoSource: fn(long) -> Pair = &intoSource;
    fThroughCall: fn(long) -> Pair = &throughCall;
    fLooped: fn(long) -> long = &looped;
    fWider: fn(long) -> Outer = &wider;
    fFieldOff: fn(long) -> Pair = &fieldOff;
    p0: Pair = mk(3);
    bump(&p0, dyn(1));
    if (p0.x != 103) { return 99; }
    bad: long = 0;
    for i in 0..20 {
        n: long = dyn(i);
        c: Pair = fChain(n);
        if (c.x != n || c.y != n * 2 || c.z != n + 5) { bad = bad | 1; }
        d: Pair = fIntoCopy(n);
        if (d.x != 7 || d.y != n * 2 || d.z != n + 5) { bad = bad | 2; }
        e: Pair = fIntoSource(n);
        if (e.x != n || e.y != 3 || e.z != n + 5) { bad = bad | 4; }
        f: Pair = fThroughCall(n);
        if (f.x != n || f.y != 4 || f.z != n + 5) { bad = bad | 8; }
        want: long = (n * 1000 + n * 2) + (n * 1000 + n * 2) + ((n + 1) * 1000 + n * 2);
        if (fLooped(n) != want) { bad = bad | 16; }
        g: Outer = fWider(n);
        if (g.p.x != n || g.p.y != n * 2 || g.p.z != n + 5 || g.w != n + 40) { bad = bad | 32; }
        h: Pair = fFieldOff(n);
        if (h.x != n + 1 || h.y != 6 || h.z != 8) { bad = bad | 64; }
    }
    return bad as int;
}
