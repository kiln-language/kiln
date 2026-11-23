// A struct taken by value that every call hands bytes nothing reads again (a value built for the
// call, or an owning local the call moves) is owned by the callee where it lies, without the
// prologue's copy. What each caller can see has to stay what the copy gave it: a value built in a
// loop and written by the callee on each turn, a local moved and assigned again, a local moved
// beside another lent to the same call, plain data that stays the caller's, a function that is
// also a fn value, one that hands its own parameter on, and a moved value whose callee raises:
// released once, by nobody here.
#include <stdlib::{core, recover, string, vec}>

var gDrops: long = 0;
struct Res { id: long, n: long }
methods Res for Drop { drop &self -> void { gDrops = gDrops + self.id; } }
struct Plain { a: long, b: long }

make id:long n:long -> Res { return Res { id: id, n: n }; }

// Writes what it owns and hands back what it saw.
bump sink r:Res -> long {
    r.n = r.n * 10 + 1;
    return r.n;
}
// A borrow beside the moved value: the borrow sees only its own.
both b:&Res sink r:Res -> long {
    r.n = r.n + 100;
    return b.n * 1000 + r.n;
}
// Plain data written: the caller's own value is untouched.
twice p:Plain -> long {
    p.a = p.a * 2;
    return p.a + p.b;
}
// Also a fn value, so a call through it may hand bytes the caller still reads.
grow p:Plain -> long {
    p.b = p.b + 1;
    return p.b;
}
// Called directly only with values built for the call, and through a fn value with a local the
// caller reads afterwards: a fn value may hold it, so it keeps its copy.
grow2 p:Plain -> long {
    p.b = p.b + 1;
    return p.b;
}
// An implementation's method: a vtable may hold it, and a call through the trait object may hand
// it a local the caller reads afterwards, so it keeps its copy too.
trait Eat { eat &self p:Plain -> long; }
struct Eater { k: long }
methods Eater for Eat { eat &self p:Plain -> long { p.a = p.a + self.k; return p.a; } }
// Hands its own parameter on.
down sink r:Res k:long -> long {
    if (k == 0) { return r.n; }
    r.n = r.n + k;
    return down(r, k - 1);
}
fail -> never { unsafe { raise(); } }
// Writes what it was handed, then raises.
spoil sink r:Res -> void {
    r.n = 0 - 1;
    fail();
}

main -> long {
    // A value built for each turn, written by the callee on each.
    total: long = 0;
    for i in 0..5 { total = total + bump(make(0, i)); }
    if (total != 105) { return 1; }

    // A local moved, written by the callee, then assigned again and moved again.
    x: Res = make(0, 3);
    if (bump(x) != 31) { return 2; }
    x = make(0, 4);
    if (bump(x) != 41) { return 3; }

    // One local lent and another moved in the same call: the borrow reads its own 7, not the
    // moved value's 107. (One local both lent and moved in a call is refused: `move_lend_err`.)
    z: Res = make(0, 7);
    y: Res = make(0, 7);
    if (both(z, y) != 7107) { return 4; }

    // Plain data stays the caller's, and so does what a fn value is handed.
    q: Plain = Plain { a: 5, b: 7 };
    s: long = twice(q) + twice(q) + q.a;
    if (s != 39) { return 5; }
    f: fn(Plain) -> long = &grow;
    if (f(q) + f(q) + grow(q) + q.b != 31) { return 6; }
    g: fn(Plain) -> long = &grow2;
    if (grow2(Plain { a: 0, b: 1 }) + g(q) + g(q) + q.b != 2 + 8 + 8 + 7) { return 11; }
    ea: Eater = Eater { k: 100 };
    if (ea.eat(Plain { a: 1, b: 0 }) != 101) { return 12; }
    te: Eat = ea;
    if (te.eat(q) != 105 || q.a != 5) { return 13; }

    // Handed on down a recursion.
    if (down(make(0, 10), 4) != 20) { return 7; }

    // Moved into a callee that writes it and raises: the caller's flag said moved before the
    // call, so the handler releases nothing, and nothing is released twice.
    gDrops = 0;
    unsafe {
        recover {
            z: Res = make(1000, 5);
            spoil(z);
        } else { }
    }
    if (gDrops != 0) { return 8; }
    // A moved value that is released, once, by its callee.
    gDrops = 0;
    d1: long = bump(make(30, 1));
    w: Res = make(400, 2);
    d2: long = bump(w);
    if (gDrops != 430 || d1 + d2 != 32) { return 9; }

    // A vector of owned values, each pushed as it is built.
    v: Vec<Res> = vec![];
    for i in 0..6 { v.push(make(0, i)); }
    acc: long = 0;
    for r in v { acc = acc + r.n; }
    if (acc != 15) { return 10; }
    return 0;
}
