// A bounds check where the length and the constants around it are more than the registers hold:
// the allocator leaves the constants without one and the emitter computes them again where they
// are read (`Emitter.materialize`), and an index past the end still stops the program (exit 134,
// the report on stderr).
var gV: long = 0;
dyn v:long -> long { gV = v; return gV; }
pick a:long b:long c:long d:long e:long f:long g:long h:long -> long { return a + 2 * b + 3 * c + 4 * d + 5 * e + 6 * f + 7 * g + 8 * h; }

walk n:long -> long {
    xs: [long; 8] = [1, 2, 3, 4, 5, 6, 7, 8];
    k1: long = 4000000000123;
    k2: long = -7000000000456;
    k3: long = 9000000000789;
    k4: long = 8100000000011;
    k5: long = 8200000000013;
    k6: long = 8300000000017;
    k7: long = 8400000000019;
    acc: long = 0;
    for i in 0..n {
        v1: long = dyn(i) * k1;
        v2: long = dyn(i) * k2;
        v3: long = dyn(i) + k3;
        v4: long = pick(i, v1, k1, k2, k3, v1, v2, v3);
        v5: long = pick(k4, k5, k6, k7, v4, k4 ^ k5, k6 ^ k7, v1);
        acc = acc + (v1 ^ v2) + (v3 & 255) + (v4 % 1000) + (v5 % 77) + xs[dyn(i)] + k1 + k2 + k3 + k4 * k5 + k6 * k7;
    }
    return acc;
}

main -> int {
    if (walk(dyn(8)) == 12345) { return 1; }      // in range: every index below 8
    if (walk(dyn(9)) == 12345) { return 2; }      // index 8: stops with 134
    return 3;
}
