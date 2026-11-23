// `k` is 2 on one path and 9 on the other: [2, 9] after the join, not inside 8 elements.
var gB: bool = true;
pick b:bool -> long {
    a: [long; 8];
    for i in 0..8 { a[i] = i; }
    k: long = 2;
    if (b) { k = 9; }
    return a[k];
}
main -> int { return pick(gB) as int; }
