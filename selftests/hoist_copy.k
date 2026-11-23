// A load the dataflow found the value of becomes a copy, and a copy of a value from outside a loop
// moves out of it with whatever reads it: a closure's captured pointer, and the load through it,
// leave the loop. Not when the loop writes the captured variable, through the closure or around
// it, and not a copy nothing moved reads.
#include <stdlib::{vec, algo}>

apply f:Fn(long) -> long n:long -> long { s: long = 0; for i in 0..n { s += f.call(i); } return s; }

scaled v:Vec<long> k:long -> long {
    scale: long = k;
    return fold(v, 0, |acc: long, x: &long| acc + x * scale);
}
// The loop writes what the closure reads, before and after each call.
moving n:long -> long {
    scale: long = 1;
    s: long = 0;
    for i in 0..n {
        scale += 1;
        s += apply(|x: long| x * scale, 3);
        scale += 10;
    }
    return s * 1000 + scale;
}
// The closure writes what it reads.
counting n:long -> long {
    hits: long = 0;
    s: long = apply(|x: long| { hits += 1; return x + hits; }, n);
    return s * 1000 + hits;
}

main -> int {
    v: Vec<long> = vec![];
    for i in 0..10 { v.push(i - 3); }
    sc: fn(Vec<long>, long) -> long = &scaled;
    if (sc(v, 3) != 45 || sc(v, -2) != -30) { return 1; }
    mv: fn(long) -> long = &moving;
    if (mv(2) != 45 * 1000 + 23) { return 2; }
    ct: fn(long) -> long = &counting;
    if (ct(4) != 16 * 1000 + 4) { return 3; }
    return 0;
}
