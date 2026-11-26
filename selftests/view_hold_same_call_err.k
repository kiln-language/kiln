// The view handed to the very call that grows its source: the call reads it while it moves.
#include <stdlib::{io, vec}>
main -> int {
    v: Vec<long>; v.push(1); v.push(2);
    s: [long] = v.asSlice();
    v.extendSlice(s);
    println("{}", v.len());
    return 0;
}
