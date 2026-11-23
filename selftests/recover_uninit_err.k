#include <stdlib::{io, recover}>

// The handler can be entered before the body assigned `x`, so `x` is not assigned there.

f -> long { unsafe { raise(); } }

main -> long {
    x: long;
    unsafe {
        recover {
            x = f();
        } else {
            println("{}", x);
        }
    }
    return 0;
}
