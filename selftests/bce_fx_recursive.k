// Two functions calling each other, the truncation only in `pong`. Whichever of the two is
// worked out second-to-last meets the other while that one is still being worked out, and that
// call answers "everything" (it is wild, and what it is handed escapes and is written all over).
// `pick` calls `ping`, the one `flow.k` works out with `pong` pending (it meets `ping`'s call to
// `pong` first), so the write two calls down is what that rule stands for: `v[2]` keeps its check
// and panics.
#include <stdlib::vec>
var gSink: long = 0;
ping inout v:Vec<long> n:long -> void {
    s: long = 0;
    for i in 0..v.len() { s = s + v.get(i) * 3 + 1; if (s > 1000) { s = s - 7; } }
    if (s == 123456789) { gSink = gSink + 1; }
    if (n > 0) { pong(&v, n - 1); }
}
pong inout v:Vec<long> n:long -> void {
    s: long = 0;
    for i in 0..v.len() { s = s + v.get(i) * 5 + 2; if (s > 1000) { s = s - 9; } }
    if (s == 987654321) { gSink = gSink + 1; }
    if (n <= 0) { v.truncate(1); return; }
    ping(&v, n - 1);
}
pick -> long {
    v: Vec<long>;
    v.push(1); v.push(2); v.push(3);
    ping(&v, 3);
    return v[2];
}
main -> int {
    w: Vec<long>;
    w.push(5); w.push(6);
    pong(&w, 2);
    a: long = pick();
    return (a + pick()) as int;
}
