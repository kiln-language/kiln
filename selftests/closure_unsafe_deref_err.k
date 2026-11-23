#include <stdlib::{io}>

// A closure written in safe code is safe code: reading through a raw pointer there needs an
// `unsafe` block, as it would anywhere else in the function around it.

viaBound<F: Fn() -> void> f:F -> void { f(); }

peek p:*long -> long {
    got: long = 0;
    viaBound(|| { got = *p; });
    return got;
}

main -> long {
    n: long = 3;
    r: long = 0;
    unsafe { r = peek(&n as *long); }
    return r;
}
