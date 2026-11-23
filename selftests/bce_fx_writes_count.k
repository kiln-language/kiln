// A callee that writes the count: what the caller knew of `v.count` (3, from its pushes) dies at
// the call, so `v[2]` keeps its check and panics. The callee is too large to be inlined and is
// called twice, so the call stays a call and its summary is what decides.
#include <stdlib::vec>
var gSink: long = 0;
shrink inout v:Vec<long> -> void {
    s: long = 0;
    for i in 0..v.len() { s = s + v.get(i) * 3 + 1; if (s > 1000) { s = s - 7; } }
    for i in 0..v.len() { s = s ^ (v.get(i) << 2); }
    if (s == 123456789) { gSink = gSink + 1; }
    v.truncate(1);
}
pick -> long {
    v: Vec<long>;
    v.push(1); v.push(2); v.push(3);
    shrink(&v);
    return v[2];
}
main -> int {
    w: Vec<long>;
    w.push(5); w.push(6);
    shrink(&w);
    a: long = pick();
    return (a + pick()) as int;
}
