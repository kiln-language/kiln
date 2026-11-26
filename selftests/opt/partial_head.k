// A call in a loop to a body too large to copy whose head returns by a short path: the head is
// copied in place (`partialPlan`), and the call is made only where the head leaves for it, here
// for the loop. Off with `--no-partial-inline`.
// ir-has: partial_head::count .PE
// ir-count: partial_head::count call partial_head::sumTo 1
sumTo n:long -> long {
    if (n <= 1) { return n; }
    s: long = 0;
    for i in 0..n + 1 { s += i; }
    return s;
}
count n:long -> long {
    t: long = 0;
    for k in 0..n { t += sumTo(k % 4 - 1); }
    return t;
}
main -> int {
    // k % 4 - 1 runs -1, 0, 1, 2: sums -1, 0, 1, 3
    if (count(8) != 6 || sumTo(10) != 55) { return 1; }
    return 0;
}
