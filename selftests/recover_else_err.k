#include <stdlib::{io, recover}>

// The handler is not optional.

main -> long {
    n: long = 0;
    unsafe { recover { n = 1; } }
    return n;
}
