// An aggregate result is built where it goes: `x = grow(n)` hands `grow` the address of `x`, and
// `grow` builds its value in the memory its `$sret` points at (the call to `lit` included). No
// block copy is left in either.
// ir-lacks: result_place::use aggcopy
// ir-lacks: result_place::lit aggcopy
// ir-lacks: result_place::grow aggcopy
// ir-has: result_place::use = addrof x
struct P { a: long, b: long, c: long }
// Too large to inline at four call sites, so `grow` calls it.
lit n:long -> P {
    i: long = 0; t: long = 0; u: long = 1;
    while (i < n) { t = t + i; i = i + 1; }
    while (i > 0) { u = u * 3 + t; i = i - 1; }
    return P { a: t, b: n, c: u - u + 1 };
}
grow n:long -> P {
    p: P = lit(n);
    i: long = 0;
    while (i < n) { p.a = p.a + p.b; i = i + 1; }
    while (i > 0) { p.c = p.c * 3 + i; i = i - 1; }
    while (i < 4) { p.b = p.b ^ (p.a + i); i = i + 1; }
    return p;
}
use n:long -> long {
    x: P = grow(n);
    y: P = lit(n + 1);
    x = grow(y.a);
    return x.a + x.b + x.c + y.c;
}
main -> int {
    t: P = grow(2);
    u: P = lit(2);
    if (t.a != 5 || t.c != 16 || u.b != 2 || use(2) != use(2)) { return 1; }
    return 0;
}
