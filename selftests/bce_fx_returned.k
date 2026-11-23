// A callee that hands back the pointer it was lent, and so is declared `unsafe`. The parameter
// escapes into its result, so the caller's `v` is exposed, and a write through the returned pointer
// (which the caller cannot tell from any other pointer) ends what it knew of `v.count`. `v[2]`
// keeps its check and panics.
#include <stdlib::vec>
var gSink: long = 0;
unsafe pass inout v:Vec<long> -> *Vec<long> {
    s: long = 0;
    for i in 0..v.len() { s = s + v.get(i) * 3 + 1; if (s > 1000) { s = s - 7; } }
    for i in 0..v.len() { s = s ^ (v.get(i) << 2); }
    if (s == 123456789) { gSink = gSink + 1; }
    return &v as *Vec<long>;
}
pick -> long {
    v: Vec<long>;
    v.push(1); v.push(2); v.push(3);
    unsafe {
        q: *Vec<long> = pass(&v);
        (*q).truncate(1);
    }
    return v[2];
}
main -> int {
    w: Vec<long>;
    w.push(5);
    unsafe { pass(&w); }
    a: long = pick();
    return (a + pick()) as int;
}
