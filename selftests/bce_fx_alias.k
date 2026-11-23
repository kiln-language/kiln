// A callee that keeps the address it is handed (a global pointer), and so is declared `unsafe`:
// `v` is exposed from then on, and a later call that writes through the kept pointer, naming no
// argument, ends what the caller knew of `v.count`. `v[2]` keeps its check and panics.
#include <stdlib::vec>
var gKept: *Vec<long> = 0 as *Vec<long>;
var gSink: long = 0;
unsafe keep inout v:Vec<long> -> void {
    s: long = 0;
    for i in 0..v.len() { s = s + v.get(i) * 3 + 1; if (s > 1000) { s = s - 7; } }
    for i in 0..v.len() { s = s ^ (v.get(i) << 2); }
    if (s == 123456789) { gSink = gSink + 1; }
    gKept = &v as *Vec<long>;
}
shrinkKept -> void {
    s: long = 0;
    unsafe {
        for i in 0..(*gKept).len() { s = s + (*gKept).get(i) * 5 + 2; if (s > 1000) { s = s - 9; } }
        if (s == 987654321) { gSink = gSink + 1; }
        (*gKept).truncate(1);
    }
}
pick -> long {
    v: Vec<long>;
    v.push(1); v.push(2); v.push(3);
    unsafe { keep(&v); }
    shrinkKept();
    return v[2];
}
main -> int {
    w: Vec<long>;
    w.push(5); w.push(6);
    unsafe { keep(&w); }
    shrinkKept();
    a: long = pick();
    return (a + pick()) as int;
}
