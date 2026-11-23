// A declaration takes an integer only by lossless widening: a `long` into a `u8` is said with `as`.
f n:long -> long { return n + 1; }
main -> int {
    n: long = f(300);
    c: u8 = n;
    return c as int;
}
