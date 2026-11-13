// A value moved inside one range-for body says nothing about a same-named declaration in a later
// loop body: handed on again (with and without a value), a scalar of that name passed by value,
// and a partly moved one. Every release counted.
#include <stdlib::{string, vec}>

var gDrops: long = 0;
struct E { s: String, n: long }
methods E for Drop { drop &self -> void { gDrops = gDrops + 1; } }
struct P { a: String, b: String }
mkE n:long -> E { return E { s: stringOf("x"), n: n }; }
twice x:long -> long { return x * 2; }
keepS s:String -> long { return s.len; }

run -> long {
    out: Vec<E>;
    for i in 0..2 { e: E = mkE(i); out.push(e); }
    rows: Vec<Vec<long>>;
    for t in 0..3 { e: Vec<long>; e.push(t); rows.push(e); }
    total: long = 0;
    for t in 0..2 { e: long = t + 5; total = total + twice(e); }
    for t in 0..2 { e: E = mkE(t); total = total + e.n; out.push(e); }
    for t in 0..2 { e: P = P { a: stringOf("ab"), b: stringOf("c") }; total = total + keepS(e.a) + e.b.len; }
    for t in 0..2 { e: P = P { a: stringOf("abc"), b: stringOf("d") }; total = total + e.a.len; }
    return out.len() * 1000 + rows.len() * 100 + total;    // 4000 + 300 + (10 + 12) + 1 + 6 + 6
}

main -> int {
    r: long = run();
    if (r != 4335) { return 1; }
    if (gDrops != 4) { return 2; }
    return 0;
}
