// A struct taken by value whose every call hands it bytes nothing reads again owns those bytes
// where they lie: its seed is the pointer it arrived as, a borrow's, and the prologue copies
// nothing. One whose call hands it a local the caller reads afterwards keeps the copy, and so
// does one a fn value may hold.
// ir-has: moved_in_place::owned (param)  :ref
// ir-has: moved_in_place::kept (param)  :struct
// ir-has: moved_in_place::held (param)  :struct
#include <stdlib::{core, string}>

struct Big { a: long, b: long, c: long, d: long, s: String }
struct Flat { a: long, b: long, c: long, d: long }
var gSink: long = 0;

big n:long -> Big { return Big { a: n, b: n + 1, c: n + 2, d: n + 3, s: stringOf("x") }; }

// Called only with values built for the call: owns them in place. Big enough to stay a call.
owned sink v:Big -> long {
    v.a = v.a + v.d;
    for i in 0..v.b { v.c = v.c ^ (i * 3); v.d = v.d + (v.c >> 1); gSink = gSink + v.d; }
    for i in 0..v.a { v.d = v.d ^ (i * 5); v.c = v.c + (v.d >> 2); gSink = gSink - v.c; }
    return v.a + v.b + v.c + v.d;
}
// Called with a plain local the caller reads again: keeps the copy.
kept v:Flat -> long {
    v.a = v.a + v.d;
    for i in 0..v.b { v.c = v.c ^ (i * 3); v.d = v.d + (v.c >> 1); gSink = gSink + v.d; }
    for i in 0..v.a { v.d = v.d ^ (i * 5); v.c = v.c + (v.d >> 2); gSink = gSink - v.c; }
    return v.a + v.b + v.c + v.d;
}
// A fn value may hold it: keeps the copy.
held v:Flat -> long {
    v.a = v.a + v.d;
    for i in 0..v.b { v.c = v.c ^ (i * 3); v.d = v.d + (v.c >> 1); gSink = gSink + v.d; }
    for i in 0..v.a { v.d = v.d ^ (i * 5); v.c = v.c + (v.d >> 2); gSink = gSink - v.c; }
    return v.a + v.b + v.c + v.d;
}

main -> long {
    t: long = owned(big(3)) + owned(big(4));
    f: Flat = Flat { a: 1, b: 2, c: 3, d: 4 };
    k: long = kept(f) + kept(f) + f.a;
    h: fn(Flat) -> long = &held;
    j: long = h(f) + held(f) + f.d;
    if (t == 0 || k == 0 || j == 0) { return 1; }
    return 0;
}
