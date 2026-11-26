// A local holding a view keeps its source borrowed while the local is used: growing the Vec can
// move its buffer out from under `s`.
#include <stdlib::{io, vec}>
main -> int {
    v: Vec<long>; v.push(11);
    s: [long] = v.asSlice();
    for i in 0..1000 { v.push(i); }
    println("{}", s[0]);
    return 0;
}
