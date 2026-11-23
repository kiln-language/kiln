// A loop that never runs must not have run any of its body: a load through a raw pointer (null
// here) and a division by a variable (zero here) are left in the loop, not hoisted ahead of the
// test that skips it. Exit 0 when neither faulted.
var gN: long = 0;
var gZ: long = 0;
var gAddr: long = 0;
reads n:long -> long {
    s: long = 0;
    unsafe {
        p: *long = gAddr as *long;
        i: long = 0;
        while (i < n) { s = s + *p; i = i + 1; }
    }
    return s;
}
divides n:long m:long d:long -> long {
    s: long = 0;
    for i in 0..n { s = s + m / d; }
    return s;
}
main -> int {
    if (reads(gN) != 0) { return 1; }
    if (divides(gN, 100, gZ) != 0) { return 2; }
    return 0;
}
