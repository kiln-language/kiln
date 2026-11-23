#include <stdlib::{io}>

// Indexing a raw pointer inside a closure written in safe code is refused.

viaObj f:Fn() -> void -> void { f(); }

second p:*long -> long {
    got: long = 0;
    viaObj(|| { got = p[1]; });
    return got;
}

main -> long {
    xs: [long; 2] = [4, 5];
    r: long = 0;
    unsafe { r = second(&xs[0] as *long); }
    return r;
}
