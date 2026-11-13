// A value below 2^62 times three can wrap past the largest long: the read keeps its check.
#include <stdlib::vec>
pick v:Vec<long> w:long -> long {
    if (w < 0 || w >= 4611686018427387904) { return 0; }
    i: long = w * 3;
    if (i >= v.len()) { return 1; }
    return v.get(i);
}
main -> int {
    v: Vec<long>;
    for i in 0..4 { v.push(i); }
    return pick(v, 3074457345618258603) as int;
}
