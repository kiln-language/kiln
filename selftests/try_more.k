// `?` nested (`f(g()?)?`), as a condition, as a statement, chained on a method, in a loop, in a
// generic function, and in code the compiler runs (a global's initializer).
#include <stdlib::{core, result, option, vec}>
var hits: long = 0;
step n:long -> Result<long, str> { if (n > 50) { return Result.Err("too big"); } return Result.Ok(n + 1); }
twice n:long -> Result<long, str> { return Result.Ok(step(step(n)?)?); }
tick -> Result<long, str> { hits = hits + 1; return Result.Ok(0); }
cond n:long -> Result<long, str> {
    if (step(n)? > 10) { return Result.Ok(1); }
    tick()?;
    return Result.Ok(2);
}
sumTo n:long -> Result<long, str> {
    t: long = 0;
    i: long = 0;
    while (i < n) {
        v: long = step(i * 20)?;
        t = t + v;
        i = i + 1;
    }
    return Result.Ok(t);
}
firstOf<T: Copy> v:Vec<Option<T>> -> Option<T> {
    x: T = v.get(0)?;
    return Option.Some(x);
}
fold -> long {
    r: Result<long, str> = twice(5);       // 7
    return r.unwrapOr(0);
}
G: long = fold();
main -> int {
    t: long = G;                                       // 7
    t = t + cond(20).unwrapOr(0);                      // 1
    t = t + cond(2).unwrapOr(0);                       // 2, hits 1
    t = t + sumTo(2).unwrapOr(0);                      // (0+1) + (20+1) = 22
    bad: Result<long, str> = sumTo(4);                 // 60 is too big
    if (bad.isOk()) { return 1; }
    if (twice(50).isOk()) { return 2; }                // 51 then 52 -> Err
    v: Vec<Option<long>> = vec![];
    v.push(Option.Some(9));
    t = t + firstOf(v).unwrapOr(0);                    // 9
    return (t + hits) as int;                          // 7 + 1 + 2 + 22 + 9 + 1 = 42
}
