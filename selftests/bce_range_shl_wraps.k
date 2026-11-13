// A value below 2^62 shifted left by two can reach the sign bit: not never negative, so the
// read through it keeps its check and panics.
#include <stdlib::vec>
pick v:Vec<long> w:long -> long {
    if (w < 0 || w >= 4611686018427387904) { return 0; }
    i: long = w << 2;
    if (i >= v.len()) { return 1; }
    return v.get(i);
}
main -> int {
    v: Vec<long>;
    for i in 0..4 { v.push(i); }
    return pick(v, 3458764513820540928) as int;
}
