// `?` reads a value implementing `Try`: a plain `long` has nothing to return early with.
#include <stdlib::{core, result}>
h -> long { return 1; }
g -> Result<long, long> { x: long = h()?; return Result.Ok(x); }
main -> long { r: Result<long, long> = g(); return r.unwrapOr(0); }
