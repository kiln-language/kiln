#include <stdlib::{core, result}>
f -> Result<long, long> { return Result.Ok(1); }
h -> long { return 2; }
add a:long b:long -> long { return a + b; }
g -> Result<long, long> { x: long = add(h(), f()?); return Result.Ok(x); }
main -> int { r: Result<long, long> = g(); return r.unwrapOr(0) as int; }
