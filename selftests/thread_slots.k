// `flow.k`'s `threadPastSlots`: an edge into a join that copies an aggregate into a slot and
// branches on a field of it is pointed straight at the target its own stored constant picks, but
// only when nothing on that path reads what the join wrote. Each function below meets the join
// with values the optimizer cannot see; the answers are checked against the arithmetic.

var gV: long = 0;
dyn v:long -> long { gV = v; return gV; }

enum Maybe<T> { Some(T), None }
struct Pair { tag: long, x: long, y: long }

look n:long -> Maybe<long> { if (n > 10) { return Maybe.None; } return Maybe.Some(n * 3); }

// The plain case: each arm uses what its own predecessor built.
one n:long -> long {
    match look(n) { Some(v) { return v - 1; } None { return -5; } }
}

// The decided target reads the copied value: the copy must stay on that path.
pairOf n:long -> Pair {
    if (n > 10) { return Pair { tag: 1, x: n, y: n + 1 }; }
    return Pair { tag: 0, x: 2 * n, y: 7 };
}
two n:long -> long {
    p: Pair = pairOf(n);
    if (p.tag == 1) { return p.x + p.y; }
    return p.x - p.y;
}

// The tag is written twice on one path: the last store decides.
pairTwice n:long -> Pair {
    q: Pair = Pair { tag: 1, x: n, y: 0 };
    if (n > 10) { q.tag = 0; q.y = 9; return q; }
    return Pair { tag: 1, x: n + 100, y: 1 };
}
three n:long -> long {
    p: Pair = pairTwice(n);
    if (p.tag == 1) { return p.x * 2 + p.y; }
    return p.x + p.y;
}

// The last store before the join is to another field, of the value the test wants: the tag's own
// store decides, and the arm it picks reads the struct, so that edge keeps the join.
pairLast n:long -> Pair {
    q: Pair = Pair { tag: 1, x: n, y: 0 };
    if (n > 10) { q.tag = 0; q.y = 1; return q; }
    return Pair { tag: 1, x: n + 100, y: 1 };
}
five n:long -> long {
    p: Pair = pairLast(n);
    if (p.tag == 1) { return 77; }
    return p.x;
}

// The tag is stored as a variable on one path: that edge is not decided.
pairVar n:long t:long -> Pair {
    if (n > 10) { return Pair { tag: t, x: n, y: 3 }; }
    return Pair { tag: 1, x: n, y: 4 };
}
four n:long t:long -> long {
    p: Pair = pairVar(n, t);
    if (p.tag == 1) { return p.x + p.y; }
    return p.x - p.y;
}

main -> int {
    bad: long = 0;
    for i in 0..30 {
        n: long = dyn(i);
        e1: long = -5;
        if (n <= 10) { e1 = n * 3 - 1; }
        if (one(n) != e1) { bad = bad | 1; }
        e2: long = 2 * n - 7;
        if (n > 10) { e2 = n + n + 1; }
        if (two(n) != e2) { bad = bad | 2; }
        e3: long = (n + 100) * 2 + 1;
        if (n > 10) { e3 = n + 9; }
        if (three(n) != e3) { bad = bad | 4; }
        t: long = dyn(i % 2);
        e4: long = n + 4;
        if (n > 10) { if (t == 1) { e4 = n + 3; } else { e4 = n - 3; } }
        if (four(n, t) != e4) { bad = bad | 8; }
        e5: long = 77;
        if (n > 10) { e5 = n; }
        if (five(n) != e5) { bad = bad | 16; }
    }
    return bad as int;
}
