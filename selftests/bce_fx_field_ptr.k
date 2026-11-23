// The caller stores `s`'s address in a struct and lends the struct: the store exposes `s`, and
// the callee, writing through the pointer it loads from the struct, writes `s.c` itself. What the
// caller knew of `s.c` (1) dies at the call, and `a[s.c]` with `s.c` now 5 keeps its check and
// panics. The callee writes no global and nothing through its parameter but `h.n`: only the write
// through the loaded pointer makes it wild.
struct S { a: long, b: long, c: long }
struct Holder { p: *S, n: long }
viaField inout h:Holder -> void {
    t: long = 0;
    unsafe {
        for i in 0..(*h.p).b { t = t + i * 3 + 1; if (t > 1000) { t = t - 7; } }
        if (t == 123456789) { h.n = 0; }
        (*h.p).c = h.n;
    }
}
pick n:long -> long {
    a: [long; 3];
    for i in 0..3 { a[i] = i; }
    s: S = S { a: 0, b: 40, c: 1 };
    h: Holder;
    unsafe { h = Holder { p: &s as *S, n: n }; }
    viaField(&h);
    return a[s.c];
}
main -> int {
    t: S = S { a: 0, b: 30, c: 0 };
    g: Holder;
    unsafe { g = Holder { p: &t as *S, n: 2 }; }
    viaField(&g);
    a: long = pick(5);
    return (a + pick(6)) as int;
}
