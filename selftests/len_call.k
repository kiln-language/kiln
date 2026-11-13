// `len()` reads the length on every string and container: a method on Vec (and the other
// containers), the `len` field of a str, a slice and a String, read through the call form.
#include <stdlib::{core, vec, string}>
struct Buf { len: long, cap: long }        // a `len` field and no `len` method: `b.len()` reads it
struct Sized { len: long }
methods Sized { len &self -> long { return self.len * 100; } }    // a method of its own wins
twice s:str -> long { return s.len() + s.len; }
main -> int {
    s: str = "hello";                      // 5
    t: String = stringOf("abc");        // 3
    v: Vec<long> = vec![1, 2];             // 2
    xs: [long; 4];
    sl: [long] = xs[..];                   // 4
    b: Buf = Buf { len: 7, cap: 9 };
    z: Sized = Sized { len: 1 };
    total: long = s.len() + t.len() + v.len() + sl.len() + b.len() + "xy".len() + twice("q");
    return (total + z.len() + t.len) as int;    // 5+3+2+4+7+2+2 = 25, + 100 + 3 = 128
}
