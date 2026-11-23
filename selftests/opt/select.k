// A branch that only chooses a value is written as conditional moves (`asm.k` `markSelects`):
// - `pick`: one `cmov`, straight from the register the chosen argument is in (rax is named only
//   by the parameter it brings and the result), and no jump.
// - `argMax`: the best so far and where it was found, two `cmov`s under one comparison; the loop's
//   only jump is its test turned round.
// - `maskOrAdd`: the arm that sets the flags (`x & 15`) is computed before the comparison, the
//   other (`x + 2`) after it with an `lea`.
// - `scale`: an arm of two instructions whose first value is its own, and the other arm: all three
//   `lea`s.
// - `stored`: an arm that stores stays a branch.
// asm-count: select::pick cmov 1
// asm-count: select::pick rax 2
// asm-lacks: select::pick j
// asm-count: select::argMax cmov 2
// asm-lacks: select::argMax jmp
// asm-count: select::argMax jl 1
// asm-count: select::maskOrAdd cmov 1
// asm-has: select::maskOrAdd and rax, 15
// asm-has: select::maskOrAdd lea
// asm-lacks: select::maskOrAdd jmp
// asm-count: select::scale lea 3
// asm-lacks: select::scale jmp
// asm-lacks: select::stored cmov
pick a:long b:long c:bool -> long { r: long = 0; if (c) { r = a; } else { r = b; } return r; }
argMax xs:[long] -> long {
    best: long = xs[0];
    at: long = 0;
    for i in 1..xs.len { v: long = xs[i]; if (v > best) { best = v; at = i; } }
    return at * 1000 + best;
}
maskOrAdd x:long c:bool -> long { r: long = 0; if (c) { r = x & 15; } else { r = x + 2; } return r; }
scale a:long b:long -> long { r: long = 0; if (a < b) { t: long = a * 5; r = t + b; } else { r = b - 4; } return r; }
stored p:*long x:long -> long { if (x > 0) { unsafe { *p = x; } } return x; }
main -> int {
    pk: fn(long, long, bool) -> long = &pick;
    am: fn([long]) -> long = &argMax;
    mo: fn(long, bool) -> long = &maskOrAdd;
    sc: fn(long, long) -> long = &scale;
    st: fn(*long, long) -> long = &stored;
    xs: [long; 5] = [3, 9, -2, 9, 4];
    cell: long = 0;
    if (pk(1, 2, true) != 1 || pk(1, 2, false) != 2 || am(xs[..]) != 1009) { return 1; }
    if (mo(-1, true) != 15 || mo(-1, false) != 1 || sc(2, 3) != 13 || sc(3, 2) != -2) { return 2; }
    unsafe {
        pc: *long = &cell as *long;
        if (st(pc, 5) != 5 || cell != 5 || st(pc, -1) != -1 || cell != 5) { return 3; }
    }
    return 0;
}
