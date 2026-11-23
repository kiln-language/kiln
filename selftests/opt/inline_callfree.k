// In a loop, a body whose copy would make no call is copied with its own calls copied in turn
// (`callFree`): `hot` takes `helper` as any small body, and `helper`'s calls to `inner` with it, so
// its loop calls nothing; nor does `hotVec`'s but on the cold path of its bounds checks.
// Outside a loop the same body is copied as before and keeps its calls (`cold`). A body that would
// still make a call, here through a fn value, stays a call (`viaFn` keeps `withFn`). A call in a
// loop of a body copied to its one call site counts as in a loop where the copy lands: `deep` takes
// `walk` whole, and once that copy has used up its budget, the calls to `step` left in `walk`'s loop
// are still copied, being call-free.
// ir-lacks: inline_callfree::hot call
// ir-lacks: inline_callfree::hotVec call vec::
// ir-has: inline_callfree::cold call inline_callfree::inner
// ir-has: inline_callfree::viaFn call inline_callfree::withFn
// ir-lacks: inline_callfree::deep call
#include <stdlib::{vec}>
inner x:long -> long { return x * 3 + 1; }
helper x:long -> long { return inner(x) ^ inner(x + 1); }
step x:long -> long { return inner(x) + inner(x + 1) + inner(x + 2) + 5; }
pair v:&Vec<long> i:long -> long { return v.get(i) * 2 + v.get(i + 1); }
withFn x:long f:fn(long) -> long -> long { return f(x) + inner(x); }
outer x:long -> long { return withFn(x, &inner) + 1; }

hot n:long -> long {
    s: long = 0;
    for i in 0..n { s += helper(i); }
    return s;
}
hotVec v:&Vec<long> -> long {
    s: long = 0;
    for i in 0..v.len() - 1 { s += pair(v, i); }
    return s;
}
cold x:long -> long { return helper(x); }
viaFn n:long -> long {
    s: long = 0;
    for i in 0..n { s += outer(i); }
    return s;
}
walk n:long -> long {
    s: long = 0;
    for i in 0..n {
        s += step(i) + step(i + 1) + step(i + 2) + step(i + 3) + step(i + 4) + step(i + 5);
        s += step(i + 6) + step(i + 7) + step(i + 8) + step(i + 9) + step(i + 10) + step(i + 11);
    }
    return s;
}
deep n:long -> long { return walk(n) + 1; }
side n:long -> long {
    t: Vec<long> = vec![1, 2];
    return step(n) + step(n + 1) + pair(&t, 0) + outer(n);
}

main -> int {
    f: fn(long) -> long = &hot;
    g: fn(long) -> long = &cold;
    h: fn(long) -> long = &viaFn;
    d: fn(long) -> long = &deep;
    e: fn(long) -> long = &side;
    hv: fn(&Vec<long>) -> long = &hotVec;
    want: long = 0;
    for i in 0..10 { want += (i * 3 + 1) ^ (i * 3 + 4); }
    if (f(10) != want) { return 1; }
    if (g(2) != (7 ^ 10)) { return 2; }
    w: long = 0;
    for i in 0..10 { w += 2 * (i * 3 + 1) + 1; }
    if (h(10) != w) { return 3; }
    k: long = 0;
    for i in 0..10 { for j in 0..12 { k += 9 * (i + j) + 17; } }
    if (d(10) != k + 1) { return 4; }
    if (e(1) != 26 + 35 + 4 + 9) { return 5; }
    v: Vec<long> = vec![1, 2, 3, 4];
    if (hv(&v) != 4 + 7 + 10) { return 6; }
    return 0;
}
