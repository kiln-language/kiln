// An element access is one addressing mode, `[base + i*scale]`: no shift and no sum left over.
// ir-lacks: scaled::sum shl
// ir-has: scaled::sum *8]
// ir-has: scaled::fill *4]
// ir-lacks: scaled::fill shl
// ir-has: scaled::bytes ptrload [t4 + t2]  :u8
// Two sums in its loop, the element and the counter, in each of the three copies of the body
// `Opt.unrollLoop` makes, and the bound put back after the loop: seven.
// ir-count: scaled::bytes = add 7
sum xs:[long] -> long { s: long = 0; for i in 0..xs.len { s = s + xs[i]; } return s; }
fill inout xs:[int] v:int -> void { for i in 0..xs.len { xs[i] = v + (i as int); } }
bytes xs:[u8] -> long { t: long = 0; for i in 0..xs.len { t = t + (xs[i] as long); } return t; }
main -> int {
    a: [long; 4] = [1, 2, 3, 4];
    b: [int; 3] = [0, 0, 0];
    fill(&b[..], 5);
    c: [u8; 3] = [7, 8, 9];
    if (sum(a[..]) != 10 || b[2] != 7 || bytes(c[..]) != 24) { return 1; }
    return 0;
}
