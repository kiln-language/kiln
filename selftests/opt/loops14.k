// What a loop's code should come to:
// - `step`: `n % 2 == 0` is a `test` of the low bit, and under it `n / 2` is one exact `sar`
//   (no rounding fix); `3 * n + 1` is two `lea`s. The `if` is no branch: both arms run and one
//   `cmov` keeps the value the test chose, so the loop's only jumps are its test at the top and
//   the same test turned round at the bottom.
// - `tally`: the arms store, so the `if` stays a branch. They meet just before the jump back, and
//   the arm that jumped there ends instead with its own copy of the counter's test, then the jump
//   out: three tests in all, with the one at the top, and one `jmp`.
// - `squares`: `(i * i) % 7` of a counter's square, never negative (the counter stays below a
//   constant, so the square cannot wrap), has no rounding fix.
// - `sieve`: a constant stored into a local array is the store's immediate, and the array's
//   address is part of the addressing mode, so nothing in the loop forms either: the only `lea`
//   of the array is the one that clears it.
// - `trial`: the header's `i * i` is computed again at the jump back (two products), and the
//   remainder by a variable uses the 32-bit divide where both operands fit.
// - `above`: the bound a closure captures is loaded once, out of the loop, and each element is
//   compared where it lies in memory.
// asm-lacks: loops14::step shr rdx, 63
// asm-lacks: loops14::step imul
// asm-lacks: loops14::step and r
// asm-lacks: loops14::step jmp
// asm-count: loops14::step cmov 1
// asm-count: loops14::step cmp r 2
// asm-count: loops14::tally jmp 1
// asm-count: loops14::tally cmp r 3
// asm-lacks: loops14::squares shr rax, 63
// asm-count: loops14::sieve [rbp - 4000] 1
// asm-has: loops14::sieve dword [rbp + r
// asm-has: loops14::sieve ], 1
// asm-count: loops14::trial imul 2
// asm-has: loops14::trial div e
// asm-has: loops14::above cmp qword [
#include <stdlib::{vec, algo}>

step n0:long -> long {
    n: long = n0;
    s: long = 0;
    while (n != 1) {
        if (n % 2 == 0) { n = n / 2; } else { n = n * 3 + 1; }
        s += 1;
    }
    return s;
}
tally n0:long -> long {
    counts: [long; 2] = [0, 0];
    n: long = n0;
    s: long = 0;
    while (n != 1) {
        if (n % 2 == 0) { counts[0] = counts[0] + 1; n = n / 2; } else { counts[1] = counts[1] + 1; n = n * 3 + 1; }
        s += 1;
    }
    return s * 1000000 + counts[0] * 1000 + counts[1];
}
squares k:long -> long { s: long = 0; for i in 0..1000 { s += (i * i) % 7 + k; } return s; }
sieve k:long -> long {
    n: long = 1000;
    xs: [int; 1000];
    for p in 2..n { if (xs[p] == 0) { m: long = p + p; while (m < n) { xs[m] = 1; m += p; } } }
    c: long = 0;
    for p in 2..n { if (xs[p] == 0) { c += 1; } }
    return c;
}
trial n:long -> long {
    i: long = 2;
    while (i * i <= n) {
        if (n % i == 0) { return 0; }
        i += 1;
    }
    return 1;
}
above v:Vec<long> lim:long -> long {
    limit: long = lim;
    return count(v, |x: &long| x > limit);
}
main -> int {
    a: fn(long) -> long = &step;
    b: fn(long) -> long = &squares;
    c: fn(long) -> long = &sieve;
    d: fn(long) -> long = &trial;
    e: fn(Vec<long>, long) -> long = &above;
    v: Vec<long> = vec![];
    for i in 0..10 { v.push(i * 7 % 10); }
    t: fn(long) -> long = &tally;
    if (a(27) != 111 || b(0) != 2001 || b(1) != 3001 || t(27) != 111070041) { return 1; }
    if (c(0) != 168 || d(97) != 1 || d(91) != 0) { return 2; }
    if (e(v, 4) != 5) { return 3; }
    return 0;
}
