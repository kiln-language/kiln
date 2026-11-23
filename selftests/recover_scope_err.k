#include <stdlib::{io, recover}>

// What the body declares is out of scope in the handler.

main -> long {
    unsafe {
        recover {
            y: long = 3;
            raise();
        } else {
            return y;
        }
    }
    return 0;
}
