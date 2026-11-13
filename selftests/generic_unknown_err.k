// `Result` without `#include <stdlib::result>`: the type is unknown, and the library has a module
// of that name. (It used to stand as a struct nobody declared: "'rr' is not a sum type".)
f -> Result<long, long> { return Result.Ok(1); }
main -> int { rr: Result<long, long> = f(); match rr { Ok(v) { return v as int; } Err(e) { return 2; } } }
