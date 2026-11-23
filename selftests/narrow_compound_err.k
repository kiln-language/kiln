// `c += n` is `c = c + n`: a `u8` plus a `long` is a `long`, and it does not go back into the `u8` unsaid.
f n:long -> long { return n + 1; }
main -> int {
    c: u8 = 1;
    c += f(2);
    return c as int;
}
