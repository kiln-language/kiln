// What a call costs, read off the assembly. `both` makes its test before anything else, with its
// argument where it arrived, and returns from there when the answer is the argument (no frame,
// no saved register); the path that recurses saves two registers and keeps no frame pointer.
// Each argument is computed straight into `rax`, where it is passed, and the second result is
// added to the first where it arrives (in `rax`). `fib` is the same with its second call a loop
// (`opt/accumulate`): the test copied ahead of the loop is still made before anything is saved.
// `pick` has no frame at all, and its parameters reach their registers by moves between
// registers, none through a slot. `keep` holds an array, so it keeps its frame. Built without
// copying a function's body into its own calls (`selfInline`), which would give `both` and `fib`
// more registers to save and fewer calls, and is held to its own shape in `opt/self_copy`.
// flags: --no-self-inline
// asm-first: frame::both cmp rax, 2
// asm-has: frame::both .GX
// asm-lacks: frame::both rbp
// asm-count: frame::both push 2
// asm-count: frame::both call 2
// asm-count: frame::both lea rax, [r 3
// asm-has: frame::both , rax
// asm-lacks: frame::both mov rax, r
// asm-first: frame::fib cmp rax, 2
// asm-has: frame::fib .GX
// asm-lacks: frame::fib rbp
// asm-count: frame::fib push 2
// asm-count: frame::fib call 1
// asm-lacks: frame::pick rbp
// asm-lacks: frame::pick rsp
// asm-lacks: frame::pick push
// asm-has: frame::keep push rbp
// Each result plus one: the sum is no longer the call's result combined with one value, so both
// calls stay calls.
both n:long -> long {
    if (n < 2) { return n; }
    return both(n - 1) + both(n - 2) + 1;
}

fib n:long -> long {
    if (n < 2) { return n; }
    return fib(n - 1) + fib(n - 2);
}

pick a:long b:long c:long -> long { return a * 3 + b * 5 + c; }

keep n:long -> long {
    xs: [long; 4] = [n, n + 1, n + 2, n + 3];
    s: long = 0;
    for i in 0..4 { s += xs[i]; }
    return s;
}

main -> int {
    f: fn(long, long, long) -> long = &pick;
    k: fn(long) -> long = &keep;
    if (fib(20) != 6765 || both(20) != 17710 || f(1, 2, 3) != 16 || k(1) != 10) { return 1; }
    return 0;
}
