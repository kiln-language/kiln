// `?` returns early as the function's own type, so that type must implement `Try`.
#include <stdlib::{core, result}>
struct P { x: long }
h -> Result<long, long> { return Result.Ok(1); }
g -> P { x: long = h()?; return P { x: x }; }
main -> long { return g().x; }
