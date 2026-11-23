#include <stdlib::{io, recover, string}>

// The body may have moved `s` before the call that raised, so the handler may not use it.

eat sink s:String -> void { }
f -> void { unsafe { raise(); } }

main -> long {
    s: String = stringOf("abc");
    unsafe {
        recover {
            eat(s);
            f();
        } else {
            println("{}", s.len());
        }
    }
    return 0;
}
