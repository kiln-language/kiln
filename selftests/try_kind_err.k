#include <stdlib::{core, result}>
f -> Result<long, long> { return Result.Ok(1); }
main -> int { x: long = f()?; return x as int; }
