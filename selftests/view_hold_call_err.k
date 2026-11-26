// A view handed back by a call that returns part of its argument still points into `v`.
#include <stdlib::{io, vec}>
first xs:[long] -> [long] { return xs[0..1]; }
main -> int {
    v: Vec<long>; v.push(11);
    s: [long] = first(v.asSlice());
    for i in 0..1000 { v.push(i); }
    println("{}", s[0]);
    return 0;
}
