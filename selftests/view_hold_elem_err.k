// An element read out of a view is a view of what the viewed place holds: `s` came from `names`,
// whose views point into `v`, so `s` holds `v` (and not `names`, gone by then).
#include <stdlib::{io, vec, string}>
main -> int {
    v: Vec<u8>; v.push(104); v.push(105);
    s: str = "";
    {
        names: Vec<str>;
        names.push(v.asSlice() as str);
        all: [str] = names.asSlice();
        s = all[0];
    }
    for i in 0..1000 { v.push(88); }
    println("{}", s);
    return 0;
}
