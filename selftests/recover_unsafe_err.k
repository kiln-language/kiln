#include <stdlib::{io, recover}>

// `recover` abandons frames without releasing what they own, so it needs `unsafe`.

main -> long {
    n: long = 0;
    recover { n = 1; } else { n = 2; }
    return n;
}
