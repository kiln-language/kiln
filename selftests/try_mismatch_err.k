#include <stdlib::{core, result, option}>
f -> Option<long> { return Option.Some(1); }
g -> Result<long, long> { x: long = f()?; return Result.Ok(x); }
main -> int { r: Result<long, long> = g(); return r.unwrapOr(0) as int; }
