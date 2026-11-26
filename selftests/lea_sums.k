// Sums the scaler makes one `lea` (`Scaler.foldArith`): a product by 3, 5 or 9 with a constant
// added or taken away, a scaled value plus a constant or another value, two values and a
// constant, a value plus another plus a constant, and a chain of them; each across the edges of
// 64-bit wrapping, where `lea` must wrap as the two instructions did. An `int` sum wraps at 32
// bits and is left alone. Every function is called from a loop with its inputs from a table, so
// nothing is folded at compile time.
mul3 x:long -> long { return x * 3 + 1; }
mul5 x:long -> long { return x * 5 - 7; }
mul9 x:long -> long { return x * 9 + 2147483647; }
far x:long -> long { return x * 3 + 2147483648; }
shl2 x:long c:long -> long { return (x << 2) + 12; }
scaled x:long y:long -> long { return y + x * 8; }
pair x:long y:long -> long { return x + y + 40; }
offs x:long y:long -> long { return y + (x - 5); }
chain x:long -> long { t: long = x * 5 + 3; return t + 100; }
narrow x:int -> int { return x * 3 + 7; }
// The value the product read is written before the sum: the sum must not read the new one.
reuse x0:long k:long -> long {
    x: long = x0;
    s: long = 0;
    for i in 0..k {
        t: long = x * 3;
        x = x + 100;
        s = s ^ (t + 1);
    }
    return s + x;
}
// Two constants that each fit `lea`'s 32-bit displacement but not their sum: two instructions.
bigChain x:long -> long { t: long = (x ^ 1) * 5 + 2000000000; return t + 2000000000; }
collatz n0:long -> long {
    n: long = n0;
    s: long = 0;
    while (n != 1) {
        if (n % 2 == 0) { n = n / 2; } else { n = n * 3 + 1; }
        s += 1;
    }
    return s;
}
main -> int {
    xs: [long; 7] = [0, 1, -1, 9223372036854775807, -9223372036854775807 - 1, 123456789, 1000000000];
    h: long = 0;
    h2: long = 0;
    h3: long = 0;
    for k in 0..7 {
        x: long = xs[k];
        y: long = xs[6 - k];
        h = h * 31 + mul3(x);
        h = h * 31 + mul5(x);
        h = h * 31 + mul9(x);
        h = h * 31 + far(x);
        h = h * 31 + shl2(x, y);
        h = h * 31 + scaled(x, y);
        h = h * 31 + pair(x, y);
        h = h * 31 + offs(x, y);
        h = h * 31 + chain(x);
        h = h * 31 + narrow(x as int);
        h2 = h2 * 31 + reuse(x, k);
        h3 = (h3 * 31) ^ bigChain(x);
    }
    if (h != 2344536468412630636) { return 1; }
    if (h2 != -9223372017650440816) { return 3; }
    if (h3 != 3462883392733920153) { return 4; }
    if (collatz(27) != 111 || collatz(97) != 118) { return 2; }
    return 0;
}
