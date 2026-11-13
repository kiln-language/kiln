// `?` on a Result in a function returning a Result, and on an Option in one returning an Option:
// the failure is returned at once (the locals in scope released on the way), the success is the
// value. In a declaration, an expression, a call's argument, a return, a condition, chained.
#include <stdlib::{core, result, option}>
var drops: long = 0;
struct R { id: long }
methods R for Drop { drop &self -> void { drops = drops + self.id; } }
parse n:long -> Result<long, long> { if (n < 0) { return Result.Err(n); } return Result.Ok(n * 2); }
make n:long -> Result<R, long> { if (n == 0) { return Result.Err(99); } return Result.Ok(R { id: n }); }
both a:long b:long -> Result<long, long> {
    keep: R = R { id: 1000 };                 // released on every way out
    x: long = parse(a)?;
    y: long = parse(b)? + 1;
    if (parse(x)? > 100) { return Result.Ok(0); }
    return Result.Ok(x + y + parse(1)?);      // 2a + 2b + 1 + 2
}
owned n:long -> Result<long, long> {
    r: R = make(n)?;                          // the R moves out of the Result
    return Result.Ok(r.id);
}
firstEven xs:long -> Option<long> {
    h: long = half(xs)?;
    return Option.Some(h + 1);
}
half n:long -> Option<long> { if (n % 2 == 1) { return Option.None; } return Option.Some(n / 2); }
main -> int {
    t: long = 0;
    a: Result<long, long> = both(3, 4);       // 6 + 9 + 2 = 17
    t = t + a.unwrapOr(-1);
    if (drops != 1000) { return 1; }
    b: Result<long, long> = both(-5, 4);      // Err(-5)
    t = t + b.unwrapErr();                    // 12
    if (drops != 2000) { return 2; }
    c: Result<long, long> = both(3, -7);      // Err(-7), after x was read
    t = t + c.unwrapErr();                    // 5
    d: Result<long, long> = owned(7);         // 7, the R released after
    t = t + d.unwrapOr(0);                    // 12
    if (drops != 3007) { return 3; }
    e: Result<long, long> = owned(0);         // Err(99)
    t = t + e.unwrapErr();                    // 111
    o: Option<long> = firstEven(10);          // 6
    t = t + o.unwrapOr(0);                    // 117
    o2: Option<long> = firstEven(3);          // None
    t = t + o2.unwrapOr(50);                  // 167
    return (t - 100) as int;                  // 67
}
