// A branch on a constant is decided before inlining and what it cuts off is deleted: the whole
// region no path reaches, labels and loops included, and nothing that a path still reaches,
// even when the dead branch jumped into the middle of it.
pub builtin atCompileTime -> bool;

var gHits: long = 0;
sumTo n:long -> long {
    s: long = 0;
    if (atCompileTime()) {
        for i in 0..n { s += 1000; }
        return s;
    }
    i: long = 0;
    while (i < n) {
        if (i == 3) { gHits += 1; }
        s += i;
        i += 1;
    }
    return s;
}
// The constant false guards a store before a loop that is reached the other way too.
mixed n:long -> long {
    s: long = 0;
    if (atCompileTime()) { s = 100; }
    for i in 0..n { s += 2; }
    if (!atCompileTime()) { s += 1; }
    return s;
}
main -> int {
    f: fn(long) -> long = &sumTo;
    g: fn(long) -> long = &mixed;
    if (f(5) != 10 || gHits != 1) { return 1; }
    if (g(4) != 9 || sumTo(0) != 0) { return 2; }
    return 0;
}
