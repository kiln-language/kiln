// The write is two calls down: `outer` hands its parameter to `inner`, which truncates. The
// summaries compose (`outer` writes what `inner` writes through the pointer it passes on), so the
// caller's `v.count` dies at the call to `outer`, and `v[2]` keeps its check and panics.
#include <stdlib::vec>
var gSink: long = 0;
inner inout v:Vec<long> -> void {
    s: long = 0;
    for i in 0..v.len() { s = s + v.get(i) * 3 + 1; if (s > 1000) { s = s - 7; } }
    for i in 0..v.len() { s = s ^ (v.get(i) << 2); }
    if (s == 123456789) { gSink = gSink + 1; }
    v.truncate(1);
}
outer inout v:Vec<long> -> void {
    s: long = 0;
    for i in 0..v.len() { s = s + v.get(i) * 5 + 2; if (s > 1000) { s = s - 9; } }
    for i in 0..v.len() { s = s ^ (v.get(i) << 3); }
    if (s == 987654321) { gSink = gSink + 1; }
    inner(&v);
}
pick -> long {
    v: Vec<long>;
    v.push(1); v.push(2); v.push(3);
    outer(&v);
    return v[2];
}
main -> int {
    w: Vec<long>;
    w.push(5); w.push(6);
    outer(&w);
    inner(&w);
    a: long = pick();
    return (a + pick()) as int;
}
