// A short loop whose every call a copy can take away, slow paths aside, is closed (`closableLoops`):
// `fill`'s loop is two appends, and each `pushStr` is copied with its `String.write`, whose growth
// check is copied as a test (`spliceGuard`) and whose `memcpy` of a literal's length is moves. Only
// the growth call is left, behind the test. In `mixed`, the loop also calls a body with a loop of
// its own, which stays a call, so the loop is not closed and `String.write` stays a call too.
// ir-lacks: inline_closed::fill call string::String_write
// ir-has: inline_closed::fill call string::String_reserve
// ir-has: inline_closed::fill .GD
// asm-lacks: inline_closed::fill rep movsb
// ir-has: inline_closed::mixed call string::String_write
#include <stdlib::{string}>
fill n:long -> long {
    s: String;
    for i in 0..n {
        s.pushStr("key=");
        s.pushStr("value;");
    }
    return s.length();
}
count s:str c:u8 -> long {
    k: long = 0;
    for i in 0..s.len { if (s[i] == c) { k += 1; } }
    return k;
}
mixed n:long -> long {
    s: String;
    k: long = 0;
    for i in 0..n {
        s.pushStr("key=");
        k += count("a=b=c", 61);
    }
    return s.length() + k;
}
main -> int {
    f: fn(long) -> long = &fill;
    g: fn(long) -> long = &mixed;
    if (f(100) != 1000) { return 1; }
    if (g(3) != 12 + 6) { return 2; }
    return 0;
}
