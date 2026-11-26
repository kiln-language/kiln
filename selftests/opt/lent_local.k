// A local whose address is lent only to a call that keeps no pointer to it is promoted, its slot
// written before the call and read back after it (`Flow.promoteLent`); one lent to a callee that
// keeps the pointer stays in its slot. `selftests/promote_lent.k` holds the cases that run.
// ir-lacks: lent_local::walk load p
// ir-lacks: lent_local::walk store p
// ir-has: lent_local::walk ptrstore [
// ir-has: lent_local::walk ptrload [
// ir-has: lent_local::kept load v

var gKept: long = 0;
var gSpin: long = 0;

advance inout x:long n:long -> long {
    s: long = 0;
    for i in 0..n {
        s = s + i;
        gSpin = gSpin ^ i;
        gSpin = gSpin + (i * 3) % 7;
        gSpin = gSpin ^ (s << 2);
        gSpin = gSpin - (i * 5) % 11;
        gSpin = gSpin ^ (s >> 1);
        gSpin = gSpin + (gSpin % 13);
    }
    x = x + n;
    return s;
}
walk n:long -> long {
    p: long = 0;
    total: long = 0;
    while (p < n) {
        total = total + advance(&p, 3);
        total = total + p * 7;
        if ((total & 1) == 0) { p = p + 1; }
    }
    return total * 1000 + p;
}
unsafe keep inout x:long -> void {
    for i in 0..2 { gSpin = gSpin + i; }
    gKept = (&x as *long) as long;
}
kept -> long {
    v: long = 5;
    unsafe {
        keep(&v);
        q: *long = gKept as *long;
        q[0] = 77;
    }
    for i in 0..(v & 1) + 1 { gSpin = gSpin ^ i; }
    return v;
}
main -> int {
    if (walk(20) != 400020) { return 1; }
    q: long = 1;
    advance(&q, 2);
    if (q != 3) { return 2; }
    if (kept() != 77 || kept() != 77) { return 3; }
    return 0;
}
