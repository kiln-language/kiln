// The source goes out of scope while its view is still used after the block.
#include <stdlib::{io, vec, string}>
main -> int {
    s: str = "";
    {
        v: Vec<u8>; v.push(104); v.push(105);
        s = v.asSlice() as str;
    }
    println("{}", s);
    return 0;
}
