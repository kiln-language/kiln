#include <stdlib::{core, result}>
f -> Result<long, str> { return Result.Ok(1); }
g -> Result<long, long> { x: long = f()?; return Result.Ok(x); }
main -> int { r: Result<long, long> = g(); return r.unwrapOr(0) as int; }
