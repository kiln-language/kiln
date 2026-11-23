// A loop that grows the index without a bound the facts see: widened to no bound at all.
var gN: long = 6;
pick n:long -> long {
    a: [long; 8];
    for i in 0..8 { a[i] = i; }
    k: long = 0;
    i: long = 0;
    while (i < n) { k = k + 2; i = i + 1; }
    return a[k];
}
main -> int { return pick(gN) as int; }
