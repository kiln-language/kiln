// A `str` is a view: the closure captures the handle, copied. Assigning to it inside the body
// would change the closure's own copy and nothing outside, so the write is refused rather than
// compiled into a no-op.
#include <stdlib::io>
main -> int {
    s: str = "abc";
    f: Fn(long) -> long = |x: long| { s = "def"; return x; };
    return 0;
}
