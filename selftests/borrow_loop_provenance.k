// A pointer that holds the address of one borrowed parameter on the first time round a loop and of
// the other on the second, with an address computed from it before it changes: what is written
// through that address may be either parameter's bytes, so the second one's field is read again
// after the write rather than taken from before it. `walk` is too big to be inlined and is called
// twice, so it is compiled with its parameters as borrows.
struct Cell { n: long, m: long }
walk a:&Cell b:&Cell -> long {
    total: long = 0;
    s: long = 0;
    for i in 0..a.n { s = s + i * 3 + 1; if (s > 1000) { s = s - 7; } }
    for i in 0..b.n { s = s ^ (i << 2); }
    unsafe {
        p: *Cell = &a as *Cell;
        for i in 0..2 {
            before: long = b.m;
            q: *long = (p as long + 8) as *long;
            *q = *q + 10;
            total = total + b.m - before;
            p = &b as *Cell;
        }
    }
    if (s == 123456789) { total = total + 1; }
    return total;
}
main -> long {
    x: Cell = Cell { n: 1, m: 2 };
    y: Cell = Cell { n: 3, m: 4 };
    r: long = walk(&x, &y);
    if (x.m != 12 || y.m != 14) { return 1; }
    if (r != 10) { return 2; }
    u: Cell = Cell { n: 5, m: 6 };
    if (walk(&y, &u) != 10 || y.m != 24 || u.m != 16) { return 3; }
    return 0;
}
