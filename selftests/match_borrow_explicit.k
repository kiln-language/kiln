// `match &x.f` and `match &x` borrow what they read: the arms bind borrows of an owning payload,
// may write through them, and the owned `x` stays whole (read, lent, moved afterwards). Without
// the `&`, `match x.f` on an owned `x` takes the field out (a partial move). Every release counted.
#include <stdlib::string>
var gDrops: long = 0;
struct Res { n: long }
methods Res for Drop { drop &self -> void { gDrops = gDrops + 1; } }
enum K { A(Res), B(long), C(String) }
struct S { k: K, n: long }
take s:S -> long { return s.n; }
run -> long {
    t: long = 0;
    x: S = S { k: K.A(Res { n: 5 }), n: 1 };
    match &x.k { A(r) { t = t + r.n; r.n = 7; } B(v) { t = t + v; } C(s) { t = t + s.len; } }
    match &x.k { A(r) { t = t + r.n * 10; } _ { } }                  // the write went through: 70
    y: K = K.C(stringOf("abcd"));
    match &y { C(s) { s.push('e'); t = t + s.len * 100; } _ { } }  // 500
    match &y { C(s) { t = t + s.len * 1000; } _ { } }               // 5000
    t = t + take(x) * 10000;                                         // x is whole: 10000
    match y { C(s) { t = t + s.len * 100000; } _ { } }              // owned: takes it, 500000
    return t;
}
main -> int {
    t: long = run();
    if (t != 5 + 70 + 500 + 5000 + 10000 + 500000) { return 1; }
    if (gDrops != 1) { return 2; }
    return 0;
}
