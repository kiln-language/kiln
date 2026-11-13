// A `&self` of a scalar or a `str` is the value: arithmetic on it is arithmetic (not a pointer
// stepped by the element's size), comparisons and casts agree, a str's `.len`, `.ptr` and bytes
// read its pair, `self.clone()` is the value, and the evaluator folds the same.
#include <stdlib::{vec, string}>
trait Num { inc &self -> long; twice &self -> long; big &self -> bool; }
methods long for Num {
    inc &self -> long { return self + 1; }
    twice &self -> long { return self * 2 + (self as long) - self; }
    big &self -> bool { return self > 100; }
}
methods int for Num {
    inc &self -> long { return (self + 1) as long; }
    twice &self -> long { return (self * 2) as long; }
    big &self -> bool { return self > 100; }
}
methods u8 for Num {
    inc &self -> long { return (self as long) + 1; }
    twice &self -> long { return (self as long) * 2; }
    big &self -> bool { return self > 100; }
}
trait Lens { lens &self -> long; first &self -> long; }
methods str for Lens {
    lens &self -> long { v: Vec<long>; v.push(self.len); return v.get(0) + self.clone().len; }
    first &self -> long { if (self.len == 0) { return -1; } return self[0] as long + self[1..].len; }

}
methods str { count &self inout v:Vec<long> -> void { v.push(self.len); } }
FOLD: long = 41.inc() + 5.twice() + "abcd".lens();
main -> int {
    bad: long = 0;
    x: long = 41;
    if (x.inc() != 42 || x.twice() != 82 || x.big() || !(200 as long).big()) { bad = bad + 1; }
    i: int = 7;
    if (i.inc() != 8 || i.twice() != 14) { bad = bad + 1; }
    b: u8 = 250;
    if (b.inc() != 251 || !b.big()) { bad = bad + 1; }
    s: str = "hello";
    if (s.lens() != 10 || "ab".lens() != 4 || s.first() != 104 + 4 || "".first() != -1) { bad = bad + 1; }
    v: Vec<long>;
    s.count(&v); t: str = "xyz"; t.count(&v);
    if (v.len() != 2 || v.get(0) != 5 || v.get(1) != 3) { bad = bad + 1; }
    if (FOLD != 42 + 10 + 8) { bad = bad + 1; }
    return bad as int;
}
