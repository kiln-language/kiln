// A struct literal that leaves fields out: an `Option` is `None`, a scalar and a plain struct are
// zero, an array is zeroed, and a type with `Default` gets its default (a `File` is closed, -1,
// not fd 0: releasing it does not close stdin). Every release counted.
#include <stdlib::{file, string, vec, option}>
var gDrops: long = 0;
var gMade: long = 0;
struct Res { n: long }
methods Res for Drop { drop &self -> void { gDrops = gDrops + 1; } }
methods Res for Default { new -> Res { gMade = gMade + 1; return Res { n: 42 }; } }
struct Cfg { w: long, h: long }
methods Cfg for Default { new -> Cfg { return Cfg { w: 80, h: 24 }; } }
struct Plain { a: long, b: int }
struct W {
    f: File, o: Option<Res>, r: Res, s: String, v: Vec<long>, c: Cfg, p: Plain, n: long, arr: [long; 3]
}
run -> long {
    w: W = W { n: 1 };
    bad: long = 0;
    if (w.f.fd != -1) { bad = bad + 1; }
    match w.o { Some(x) { bad = bad + 1; } None { } }
    if (w.r.n != 42 || w.s.len != 0 || w.v.len() != 0) { bad = bad + 1; }
    if (w.c.w != 80 || w.c.h != 24 || w.p.a != 0 || w.p.b != 0 || w.arr[2] != 0) { bad = bad + 1; }
    w.v.push(3);
    x: W = W { r: Res { n: 7 }, n: 2, c: Cfg { w: 1, h: 2 } };
    if (x.r.n != 7 || x.c.w != 1) { bad = bad + 1; }
    return bad;
}
main -> int {
    bad: long = run();
    if (bad != 0) { return bad as int; }
    if (gMade != 1 || gDrops != 2) { return 10; }
    return 0;
}
