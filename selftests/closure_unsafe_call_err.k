#include <stdlib::{io}>

// Calling an `unsafe` function from a closure written in safe code is refused.

viaObj f:Fn() -> void -> void { f(); }

unsafe raw p:*long -> long { return *p; }

through p:*long -> long {
    out: long = 0;
    viaObj(|| { out = raw(p); });
    return out;
}

main -> long {
    n: long = 7;
    r: long = 0;
    unsafe { r = through(&n as *long); }
    return r;
}
