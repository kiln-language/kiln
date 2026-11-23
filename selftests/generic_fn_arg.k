#include <stdlib::{vec, map, option, string}>

// A fn type as a type argument: `Vec<fn(long) -> long>`, a map's values, an `Option`, a slice of
// them, a struct parameterized over one. Inside the generic body `*T` and `[T]` stand for the fn
// type, which has to be read back out of their spelling.

struct P { a: long, b: long }
struct Box1<T> { v: T }
methods Box1<T> { get &self -> T { return self.v; } }

dbl x:long -> long { return x * 2; }
inc x:long -> long { return x + 1; }
sumP p:&P -> long { return p.a + p.b; }
mkP n:long -> P { return P { a: n, b: n + 1 }; }
isLong s:&String -> bool { return s.len() > 3; }

applyAll fs:[fn(long) -> long] x:long -> long {
    t: long = 0;
    for f in fs { t = t + f(x); }
    return t;
}

main -> long {
    v: Vec<fn(long) -> long> = vec![];
    v.push(&dbl);
    v.push(&inc);
    if (v.len() != 2) { return 1; }
    f0: fn(long) -> long = v[0];
    f1: fn(long) -> long = v.get(1);
    if (f0(10) != 20 || f1(10) != 11) { return 2; }
    if (applyAll(v.asSlice(), 5) != 16) { return 3; }
    last: fn(long) -> long = v.pop();
    if (last(1) != 2 || v.len() != 1) { return 4; }

    m: HashMap<str, fn(long) -> long> = map![];
    m.put("dbl", &dbl);
    m.put("inc", &inc);
    g: Option<fn(long) -> long> = m.find("inc");
    match g { Some(h) { if (h(41) != 42) { return 5; } } None { return 6; } }
    if (m.find("nope").isSome()) { return 7; }

    ps: Vec<fn(&P) -> long> = vec![];
    ps.push(&sumP);
    p: P = P { a: 3, b: 4 };
    sp: fn(&P) -> long = ps[0];
    if (sp(p) != 7) { return 8; }
    mk: Vec<fn(long) -> P> = vec![];
    mk.push(&mkP);
    mk0: fn(long) -> P = mk[0];
    q: P = mk0(5);
    if (q.a != 5 || q.b != 6) { return 9; }
    ss: Vec<fn(&String) -> bool> = vec![];
    ss.push(&isLong);
    s: String = String.new();
    s.pushStr("hello");
    s0: fn(&String) -> bool = ss[0];
    if (!s0(s)) { return 10; }

    b: Box1<fn(long) -> long> = Box1 { v: &dbl };
    bg: fn(long) -> long = b.get();
    if (bg(21) != 42) { return 11; }
    return 0;
}
