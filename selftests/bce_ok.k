// The shapes whose checks the optimizer removes still compute the right thing: a counted loop
// over a vector, a slice and an array, the same index read twice, a fixed array at a constant
// index, reads after a store through the element pointer, and a self tail call 10^7 deep.
#include <stdlib::vec>
sumVec v:Vec<long> -> long { s: long = 0; for i in 0..v.len() { s = s + v.get(i); } return s; }
sumSlice xs:[long] -> long { s: long = 0; for i in 0..xs.len { s = s + xs[i]; } return s; }
dbl inout v:Vec<long> -> void { for i in 0..v.len() { v.set(i, v.get(i) * 2); } }
probe v:Vec<long> h:long -> long {
    if (v.get(h) != 0 && v.get(h) != 99) { return v.get(h); }
    return -1;
}
down n:long acc:long -> long { if (n == 0) { return acc; } return down(n - 1, acc + 1); }
main -> int {
    v: Vec<long>;
    for i in 0..10 { v.push(i); }
    a: [long; 6];
    for i in 0..6 { a[i] = i * i; }
    bad: long = 0;
    if (sumVec(v) != 45) { bad = bad + 1; }
    if (sumSlice(a[..]) != 55 || a[5] != 25 || a[0] != 0) { bad = bad + 2; }
    dbl(&v);
    if (sumVec(v) != 90 || v.get(9) != 18) { bad = bad + 4; }
    if (probe(v, 3) != 6 || probe(v, 0) != -1) { bad = bad + 8; }
    unsafe { p: *long = v.buf.ptr; p[4] = 77; }
    if (v.get(4) != 77 || sumVec(v) != 90 - 8 + 77) { bad = bad + 16; }
    if (down(10000000, 0) != 10000000) { bad = bad + 32; }
    return bad as int;
}
