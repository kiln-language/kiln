// A callee that stores one parameter into another's memory (`h.p = &v`), and so is declared
// `unsafe`: `v`'s pointer escapes through a store, so the caller's `v` is exposed, and a later call
// that writes through the stored pointer ends what the caller knew of `v.count`. `v[2]` keeps its
// check and panics.
#include <stdlib::vec>
struct Holder { p: *Vec<long>, n: long }
var gSink: long = 0;
unsafe stash inout h:Holder inout v:Vec<long> -> void {
    s: long = 0;
    for i in 0..v.len() { s = s + v.get(i) * 3 + 1; if (s > 1000) { s = s - 7; } }
    for i in 0..v.len() { s = s ^ (v.get(i) << 2); }
    if (s == 123456789) { gSink = gSink + 1; }
    h.p = &v as *Vec<long>;
}
viaField inout h:Holder -> void {
    s: long = 0;
    unsafe {
        for i in 0..(*h.p).len() { s = s + (*h.p).get(i) * 5 + 2; if (s > 1000) { s = s - 9; } }
        if (s == 987654321) { gSink = gSink + 1; }
        (*h.p).truncate(h.n);
    }
}
pick -> long {
    v: Vec<long>;
    v.push(1); v.push(2); v.push(3);
    h: Holder;
    unsafe { h = Holder { p: 0 as *Vec<long>, n: 1 }; }
    unsafe { stash(&h, &v); }
    viaField(&h);
    return v[2];
}
main -> int {
    w: Vec<long>;
    w.push(5); w.push(6);
    g: Holder;
    unsafe { g = Holder { p: 0 as *Vec<long>, n: 2 }; }
    unsafe { stash(&g, &w); }
    viaField(&g);
    a: long = pick();
    return (a + pick()) as int;
}
