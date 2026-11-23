#include <stdlib::{io, recover}>

// `raise` is `unsafe`: where it is called is where a raise starts, and the caller vouches that it
// and the `recover` that catches it own every frame in between.

check n:long -> long {
    if (n < 0) { raise(); }
    return n;
}

main -> long {
    r: long = 0;
    unsafe {
        recover { r = check(-1); } else { r = 5; }
    }
    return r;
}
