#include <stdlib::io>

// A `recover` statement needs its runtime, which `stdlib::recover` provides.

main -> long {
    n: long = 0;
    unsafe { recover { n = 1; } else { n = 2; } }
    return n;
}
