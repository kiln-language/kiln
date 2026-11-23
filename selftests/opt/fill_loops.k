// A loop that only clears a range of a frame slot's array is one block zero (`Opt.fillLoop`):
// `rep stosq` for the 4000 bytes of `a`. A loop that stores something else stays a loop.
// ir-has: fill_loops::clear aggzero
// ir-lacks: fill_loops::clear jmp
// asm-has: fill_loops::clear rep stosq
// ir-has: fill_loops::ones jmp
var gK: long = 3;
clear k:long -> long {
    a: [int; 1000];
    a[k] = 7;
    a[999] = 9;
    for i in 0..1000 { a[i] = 0; }
    return a[k] + a[999] + 1;
}
ones k:long -> long {
    a: [int; 100];
    for i in 0..100 { a[i] = 1; }
    return a[k];
}
main -> int {
    f: fn(long) -> long = &clear;
    g: fn(long) -> long = &ones;
    if (f(gK) != 1) { return 1; }
    if (g(gK) != 1) { return 2; }
    return 0;
}
