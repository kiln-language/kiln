#include <stdlib::{io, recover}>

// `recover` abandons frames without releasing what they own, so it needs `unsafe`, in a closure
// written in safe code as anywhere else.

run<F: Fn() -> void> f:F -> void { f(); }

main -> long {
    n: long = 0;
    run(|| { recover { n = 1; raise(); } else { n = n + 5; } });
    return n;
}
