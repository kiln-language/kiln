#include <stdlib::{vec, algo}>

// Two adjacent loops over one range run as one (`Opt.fuseOne`), and the pairs that must not
// be. Each pair below but the first would be fused if the one rule it breaks were not checked:
// different bounds, different starts, the second reading what the first computed, a store
// into what the other reads, a call that writes what the other reads. Their bodies make no
// bounds check, so that rule is not what keeps them apart. Every answer is what the program
// gives built without fusion (`--no-fuse`).

var gSide: long = 0;
var gAcc: long = 0;

// A loop: never copied into its callers, so a loop calling it holds a call.
local bump x:long -> long {
    for j in 0..(x & 1) + 1 { gSide = gSide + x; }
    return gSide;
}

main -> int {
    v: Vec<long> = vec![];
    for i in 0..1000 { v.push((i * 2654435761) % 977); }
    n: long = v.len();
    // Fused: a fold and a count, as `higher` has them.
    sum: long = 0;
    hits: long = 0;
    for r in 0..3 {
        sum = fold(v, sum, |acc: long, x: &long| acc + (x * 3) % 1000);
        hits += count(v, |x: &long| x > 500);
    }
    if (sum != 1462956 || hits != 1455) { return 1; }
    // Not fused: the second stops one short.
    m: long = n - 1;
    a: long = 0;
    b: long = 0;
    for i in 0..n { a = a + i * 3; }
    for i in 0..m { b = b + i * 5 + 1; }
    if (a != 1498500 || b != 2493504) { return 2; }
    // Not fused: the second reads the first's total.
    c: long = 0;
    d: long = 0;
    for i in 0..n { c = c + i * 7; }
    for i in 0..n { if (i * n * 5 > c) { d = d + 1; } }
    if (c != 3496500 || d != 300) { return 3; }
    // Not fused: the first stores what the second reads.
    e: long = 0;
    for i in 0..n { gAcc = gAcc + i; }
    for i in 0..n { e = e + gAcc % 1000; }
    if (e != 500000) { return 4; }
    // Not fused: the second calls what writes a global the first reads.
    f: long = 0;
    g: long = 0;
    for i in 0..n { f = f + gSide; }
    for i in 0..n { g = g + bump(i & 3); }
    if (f != 0 || g != 1249000) { return 5; }
    if (bump(0) != gSide) { return 7; }
    // Not fused: the second starts one later.
    h: long = 0;
    k: long = 0;
    for i in 0..n { h = h + (i & 7) + 1; }
    for i in 1..n { k = k + (i & 7) + 1; }
    if (h != 4500 || k != 4499) { return 6; }
    return 0;
}
