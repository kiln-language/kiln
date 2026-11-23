// A borrowed parameter's bytes written through an address derived from it by arithmetic other
// than adding or taking away an offset: a mask, a pair of shifts. What comes out may still point
// into the parameter, and the write must end what was known of it. Each check reads a field,
// writes 5 into it and reads it again (1 + 5). Exits with the number of the first check that fails.
#include <stdlib::{io}>

struct P { a: long, b: long }

var gDepth: long = 1;

masked inout p:P n:long -> long {
    if (n > 0) { return masked(&p, n - 1); }
    t: long = p.a;
    unsafe { q: *long = ((&p.a) as long & ~7) as *long; q[0] = 5; }
    return t + p.a;
}

shifted inout p:P n:long -> long {
    if (n > 0) { return shifted(&p, n - 1); }
    t: long = p.a;
    unsafe { q: *long = (((&p.a) as long >> 3) << 3) as *long; q[0] = 5; }
    return t + p.a;
}

main -> int {
    x: P = P { a: 1, b: 2 };
    r: long = masked(&x, gDepth);
    println("{}", r);
    if (r != 6) { return 1; }
    x.a = 1;
    r = shifted(&x, gDepth);
    println("{}", r);
    if (r != 6) { return 2; }
    return 0;
}
