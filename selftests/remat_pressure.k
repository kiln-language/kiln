// More values live at once than there are registers, many of them constants and addresses: the
// allocator spills those first and the emitter computes them again where they are read
// (`RegAlloc.markRemat`, `Emitter.materialize`): as a copy's source, a branch's operand, a bounds
// check's length, a call's argument, a shift's count, a block copy's address. Checked against the
// same arithmetic done one value at a time.

var gV: long = 0;
dyn v:long -> long { gV = v; return gV; }
pick a:long b:long c:long d:long e:long f:long g:long h:long -> long { return a + 2 * b + 3 * c + 4 * d + 5 * e + 6 * f + 7 * g + 8 * h; }

struct Big { a: long, b: long, c: long, d: long }

spread n:long -> long {
    xs: [long; 8] = [1, 2, 3, 4, 5, 6, 7, 8];
    ys: [long; 8] = [8, 7, 6, 5, 4, 3, 2, 1];
    k1: long = 4000000000123;
    k2: long = -7000000000456;
    k3: long = 9000000000789;
    big: Big = Big { a: n, b: n + 1, c: n + 2, d: n + 3 };
    acc: long = 0;
    for i in 0..n {
        j: long = i % 8;
        v1: long = xs[j] * k1;
        v2: long = ys[j] * k2;
        v3: long = (i << (j + 1)) + k3;
        v4: long = pick(xs[j], ys[j], k1, k2, k3, v1, v2, v3);
        copy: Big = big;
        copy.a = copy.a + i;
        v5: long = copy.a + copy.b * copy.c - copy.d;
        if (k3 != 0) { acc = acc + (v1 ^ v2) + (v3 & 255) + (v4 % 1000) + v5; }
        acc = acc + xs[(j + 3) % 8] - ys[(j + 5) % 8];
    }
    return acc;
}

spreadSlow n:long -> long {
    acc: long = 0;
    for i in 0..n {
        j: long = i % 8;
        x: long = dyn(j + 1);
        y: long = dyn(8 - j);
        v1: long = x * 4000000000123;
        v2: long = y * -7000000000456;
        v3: long = (i << (j + 1)) + 9000000000789;
        v4: long = x + 2 * y + 3 * 4000000000123 + 4 * -7000000000456 + 5 * 9000000000789 + 6 * v1 + 7 * v2 + 8 * v3;
        v5: long = (n + i) + (n + 1) * (n + 2) - (n + 3);
        acc = acc + (v1 ^ v2) + (v3 & 255) + (v4 % 1000) + v5;
        acc = acc + ((j + 3) % 8 + 1) - (8 - (j + 5) % 8);
    }
    return acc;
}

main -> int {
    for n in 0..40 {
        m: long = dyn(n);
        if (spread(m) != spreadSlow(m)) { return 1; }
    }
    return 0;
}
