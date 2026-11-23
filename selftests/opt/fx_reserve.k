// Interprocedural memory effects (`effects.k`): after three pushes, `v`'s count is known to be
// 3 across the `RawVec.reserve` each push calls on its growth path, which writes only the
// buffer pointer and the capacity of the `RawVec` it is lent. `v[1]` and `v.get(2)` keep no
// check; a struct field a callee does not write reads back as the value stored.
// ir-lacks: fx_reserve::three panicIndex
// ir-lacks: fx_reserve::keepC ptrload
#include <stdlib::vec>
struct S { a: long, b: long, c: long }
var gSink: long = 0;
setB inout s:S v:long -> void {
    t: long = 0;
    for i in 0..v { t = t + i * 3 + 1; if (t > 1000) { t = t - 7; } }
    if (t == 123456789) { gSink = gSink + 1; }
    s.b = v;
}
three -> long {
    v: Vec<long>;
    v.push(1); v.push(2); v.push(3);
    return v[1] + v.get(2);
}
keepC v:long -> long {
    s: S = S { a: 1, b: 2, c: 3 };
    setB(&s, v);
    return s.c + s.a;
}
main -> int {
    t: S = S { a: 0, b: 0, c: 0 };
    setB(&t, 4);
    if (three() != 5 || keepC(5) != 4 || t.b != 4) { return 1; }
    return 0;
}
