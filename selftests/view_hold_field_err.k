// A view in a local struct's field holds its source as a view local does.
#include <stdlib::{io, vec, string}>
struct Hold { s: str, n: long }
main -> int {
    v: Vec<u8>; v.push(104); v.push(105);
    h: Hold = Hold { s: v.asSlice() as str, n: 1 };
    for i in 0..1000 { v.push(88); }
    println("{}", h.s);
    return 0;
}
