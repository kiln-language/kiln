// What fits a fn type (batch 9): the same arguments taken the same way and the same result. A
// struct and a borrow of it are one argument; a `sink` on a parameter that owns nothing changes
// only whether the callee copies; a fn-typed parameter is held to the same rule.
#include <stdlib::io>
var gDrops: long = 0;
struct P { x: long, y: long }
struct Res { id: long }
methods Res for Drop { drop &self -> void { gDrops = gDrops + 1; } }
struct Keep { r: Res }
bump p:P -> long { p.x = p.x + 100; return p.x; }          // writes its own copy: a sink
peek p:&P -> long { return p.x; }
keepSink sink p:P -> long { return p.y; }
look r:Res -> long { return r.id; }
stash sink r:Res -> long { k: Keep = Keep { r: r }; return k.r.id; }
apply f:fn(P)->long p:&P -> long { return f(p); }
// A borrow in one, a struct in the other, and a `sink` on a type that owns nothing: one contract.
pair p:P q:P -> long { return p.x + q.y; }
twice n:long -> long { return n * 2; }
higher g:fn(long)->long n:long -> long { return g(n); }
gLook: fn(Res)->long = &look;
gHigh: fn(fn(long)->long, long)->long = &higher;
main -> int {
    q: P = P { x: 1, y: 2 };
    f: fn(P)->long = &bump;
    if (f(q) != 101 || q.x != 1) { return 1; }                 // the callee's write is its own
    f = &peek;
    if (f(q) != 1) { return 2; }
    s: fn(sink P)->long = &peek;                               // P owns nothing: either fits
    if (s(q) != 1) { return 3; }
    s = &keepSink;
    if (s(q) != 2) { return 4; }
    if (apply(&keepSink, q) != 2) { return 5; }
    if (true) { r: Res = Res { id: 7 }; if (gLook(r) != 7) { return 6; } }
    if (gDrops != 1) { return 7; }
    t: fn(sink Res)->long = &stash;
    if (true) { r: Res = Res { id: 8 }; if (t(r) != 8) { return 8; } }
    if (gDrops != 2) { return 9; }
    if (gHigh(&twice, 21) != 42) { return 10; }
    pr: fn(&P, sink P)->long = &pair;
    if (pr(q, q) != 3) { return 11; }
    return 0;
}
