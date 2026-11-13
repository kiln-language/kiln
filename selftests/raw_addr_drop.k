// A local whose raw address is taken is still released at its scope's end. Taking an address
// is unsafe and transfers nothing; one declared without a value and filled through its address
// (`memcpy(&gone as long, ...)`, the way an element is taken out of raw storage) holds that value
// from then on and is released like any other. Every release counted.
#include <stdlib::{mem, heap}>
var gDrops: long = 0;
struct T { v: long }
methods T for Drop { drop &self -> void { gDrops = gDrops + self.v; } }

takeOut p:*T -> long {
    gone: T;
    unsafe { memcpy(&gone as long, p as long, sizeof(T)); }
    return gone.v;                                    // released here: 1000
}
run -> long {
    {
        a: T = T { v: 10 };
        unsafe { p: long = &a as long; }              // looked at, still a's: 10
        b: T = T { v: 100 };
        unsafe { q: *T = &b as *T; q.v = 200; }       // written through, still b's: 200
        c: T;
        if (gDrops == 0) { unsafe { r: *T = &c as *T; r.v = 3; } }   // filled on one path
        else { c = T { v: 4 }; }
    }
    raw: *T = 0 as *T;
    unsafe { raw = malloc(sizeof(T)) as *T; raw.v = 1000; }
    n: long = takeOut(raw);
    unsafe { free(raw as long); }
    return n;
}
main -> int {
    n: long = run();
    if (n != 1000) { return 1; }
    if (gDrops != 10 + 200 + 3 + 1000) { return 2; }
    return 0;
}
