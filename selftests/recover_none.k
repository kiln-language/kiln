#include <stdlib::{io, recover}>

// A `raise` with no `recover` armed is a panic: it says so and exits with SIGABRT's status,
// "panic: raise: no `recover` is armed on this thread".

main -> long {
    unsafe { raise(); }
}
