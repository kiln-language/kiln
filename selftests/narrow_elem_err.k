// An element store is a store.
f n:long -> long { return n + 1; }
main -> int {
    xs: [u16; 3] = [1, 2, 3];
    xs[1] = f(7);
    return xs[1] as int;
}
