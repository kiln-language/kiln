// What a function may do with an owning global instead of moving it: borrow it, clone it, or
// take it out with `take`, which leaves an empty value behind.
#include <stdlib::{mem, vec}>
var gL: Vec<long> = vec![];
look v:&Vec<long> -> long { return v.len(); }
main -> long {
    gL.push(3); gL.push(4);
    c: Vec<long> = gL.clone();
    n: long = look(&gL);
    t: Vec<long> = take(&gL);
    gL.push(9);
    return c.len() * 10 + n + t.get(1) * 10 + gL.len() * 100;
}
