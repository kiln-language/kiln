// What a call's summary lets the caller keep, and what it must not: a field the callee does not
// write reads back as stored; one it writes, through its parameter, through a parameter passed on,
// as a whole-struct copy or at an offset it computes, reads back as written. Each callee is too
// large to inline and called from two places. 0 when every value is right.
#include <stdlib::vec>
struct S { a: long, b: long, c: long, xs: [long; 4] }
var gSink: long = 0;
var gI: long = 2;
noise inout s:S -> long {
    t: long = 0;
    for i in 0..4 { t = t + s.xs[i] * 3 + 1; if (t > 1000) { t = t - 7; } }
    if (t == 123456789) { gSink = gSink + 1; }
    return t;
}
setB inout s:S v:long -> void { noise(&s); noise(&s); s.b = v; }
viaInner inout s:S v:long -> void { noise(&s); setB(&s, v); s.a = s.a + 0; }
whole inout s:S -> void { noise(&s); s = S { a: 70, b: 71, c: 72, xs: [1, 2, 3, 4] }; }
atIndex inout s:S i:long v:long -> void { noise(&s); s.xs[i] = v; }
check1 -> long {
    s: S = S { a: 1, b: 2, c: 3, xs: [0, 0, 0, 0] };
    setB(&s, 20);
    if (s.a != 1 || s.b != 20 || s.c != 3) { return 1; }
    viaInner(&s, 30);
    if (s.a != 1 || s.b != 30 || s.c != 3) { return 2; }
    whole(&s);
    if (s.a != 70 || s.b != 71 || s.c != 72 || s.xs[3] != 4) { return 3; }
    atIndex(&s, gI, 50);
    if (s.xs[2] != 50 || s.xs[1] != 2 || s.c != 72) { return 4; }
    return 0;
}
check2 -> long {
    v: Vec<long>;
    v.push(1); v.push(2); v.push(3);
    s: S = S { a: 4, b: 5, c: 6, xs: [9, 9, 9, 9] };
    setB(&s, v[2]);
    atIndex(&s, 0, v.get(1));
    if (s.b != 3 || s.xs[0] != 2 || v.len() != 3) { return 5; }
    return 0;
}
main -> int {
    r: long = check1();
    if (r != 0) { return r as int; }
    return check2() as int;
}
