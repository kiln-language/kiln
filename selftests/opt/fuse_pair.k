#include <stdlib::{vec, algo}>

// A sum and a count over one vector, one after the other: one loop (`Opt.fuseOne`). With
// different bounds they stay two.
// asm-count: fuse_pair::both .LR 2
// asm-count: fuse_pair::apart .LR 4
both v:Vec<long> -> long {
    s: long = 0;
    c: long = 0;
    for i in 0..v.len() { s = s + v[i] * 3; }
    for i in 0..v.len() { if (v[i] > 10) { c = c + 1; } }
    return s * 1000 + c;
}
apart v:Vec<long> n:long -> long {
    s: long = 0;
    c: long = 0;
    for i in 0..n { s = s + v[i] * 3; }
    for i in 0..n - 1 { if (v[i] > 10) { c = c + 1; } }
    return s * 1000 + c;
}
main -> int {
    v: Vec<long> = vec![];
    for i in 0..20 { v.push(i); }
    if (both(v) != 570009 || apart(v, 20) != 570008) { return 1; }
    if (both(v) != 570009 || apart(v, 20) != 570008) { return 2; }
    return 0;
}
