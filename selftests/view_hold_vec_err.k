// Views pushed into a Vec<str> make the Vec hold their source too.
#include <stdlib::{io, vec, string}>
main -> int {
    v: Vec<u8>; v.push(104); v.push(105);
    names: Vec<str>;
    names.push(v.asSlice() as str);
    for i in 0..1000 { v.push(88); }
    println("{}", names.get(0));
    return 0;
}
