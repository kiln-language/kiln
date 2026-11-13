// Two values each known to be below a bound and not negative, whose sum can still pass the
// largest long: the bound is too high for `a + b` to be called never negative, and the read
// through the wrapped sum must panic.
#include <stdlib::vec>
pick v:Vec<long> a:long b:long -> long {
    if (a < 0 || b < 0 || a >= 6000000000000000000 || b >= 6000000000000000000) { return 0; }
    i: long = a + b;
    if (i >= v.len()) { return 1; }
    return v.get(i);
}
main -> int {
    v: Vec<long>;
    for i in 0..4 { v.push(i); }
    return pick(v, 5000000000000000000, 5000000000000000000) as int;
}
