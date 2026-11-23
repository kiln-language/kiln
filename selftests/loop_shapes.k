// Loops turned round where the header computes before its test (`while (i * i <= n)`, a length
// loaded, a value the test is fused with), and loops whose last block is where an `if`'s arms
// meet, which each arm then ends with a copy of. Zero and one trips, `break` and `continue`,
// early returns from nested loops, counters read after the loop, narrow counters that wrap, a
// test written back to front (`if (c) goto A; goto B; A:`), and a float test that must not be.
#include <stdlib::vec>

// The header squares the counter before its test.
isqrt n:long -> long { i: long = 0; while (i * i <= n) { i += 1; } return i - 1; }
firstFactor n:long -> long {
    i: long = 2;
    while (i * i <= n) {
        if (n % i == 0) { return i; }
        i += 1;
    }
    return n;
}
// The header reads a length the body changes.
grow n:long -> long {
    v: Vec<long> = vec![];
    v.push(1);
    i: long = 0;
    while (i < v.len()) {
        if (v.len() < n) { v.push(v.get(i) * 2); }
        i += 1;
    }
    return v.len() * 1000 + v.get(v.len() - 1);
}
// The header's test is fused with the value it reads.
twos x0:long -> long { x: long = x0; k: long = 0; if (x == 0) { return -1; } while ((x & 1) == 0) { x = x / 2; k += 1; } return k * 1000 + x; }
// Arms meeting before the jump back: two, three, and one that ends in `continue`.
collatz n0:long -> long {
    n: long = n0;
    s: long = 0;
    while (n != 1) {
        if (n % 2 == 0) { n = n / 2; } else { n = n * 3 + 1; }
        s += 1;
    }
    return s;
}
three n:long -> long {
    s: long = 0;
    i: long = 0;
    while (i < n) {
        if (i % 3 == 0) { s += 1; } else if (i % 3 == 1) { s += 10; } else { s += 100; }
        i += 1;
    }
    return s * 1000 + i;
}
skips n:long -> long {
    s: long = 0;
    i: long = 0;
    while (i < n) {
        i += 1;
        if (i % 4 == 0) { s -= 1; continue; } else { s += i; }
    }
    return s;
}
// A narrow counter that wraps, arms meeting before the jump back.
wraps start:u8 -> long {
    i: u8 = start;
    a: long = 0;
    b: long = 0;
    while (i != 5) {
        if ((i & 1) == 0) { a += 1; } else { b += 1; }
        i += 1;
    }
    return a * 1000 + b;
}
// Early return from a nested loop, and a counter read after the loop.
findPair xs:[long] target:long -> long {
    for i in 0..xs.len {
        j: long = i + 1;
        while (j < xs.len) {
            if (xs[i] + xs[j] == target) { return i * 100 + j; }
            j += 1;
        }
    }
    return -1;
}
lastIndex n:long -> long { i: long = 0; while (i * 3 < n) { if (i == 50) { break; } i += 1; } return i; }
// A flag tested at the top.
flagLoop n:long -> long { go: bool = n > 0; k: long = 0; while (go) { k += 1; if (k >= n) { go = false; } else { go = true; } } return k; }
// `if (c) goto A; goto B; A:` with an integer test, a bool, and a float, whose test must stay as
// written: a NaN fails both `<` and its negation.
pick x:long -> long { if (x > 3) { return 1; } else { return 2; } }
pickFlag b:bool -> long { if (b) { return 1; } return 2; }
pickFloat x:f64 -> long { if (x < 1.0) { return 1; } else { return 2; } }

main -> int {
    sq: fn(long) -> long = &isqrt;
    ff: fn(long) -> long = &firstFactor;
    if (sq(0) != 0 || sq(1) != 1 || sq(15) != 3 || sq(16) != 4 || sq(1000000) != 1000) { return 1; }
    if (ff(91) != 7 || ff(97) != 97 || ff(4) != 2 || ff(1) != 1) { return 2; }
    gr: fn(long) -> long = &grow;
    if (gr(1) != 1001 || gr(5) != 5016) { return 3; }
    tw: fn(long) -> long = &twos;
    if (tw(-24) != 3000 - 3 || tw(24) != 3003 || tw(7) != 7 || tw(0) != -1) { return 4; }
    cz: fn(long) -> long = &collatz;
    if (cz(27) != 111 || cz(1) != 0 || cz(2) != 1) { return 5; }
    th: fn(long) -> long = &three;
    if (th(7) != 223007 || th(0) != 0 || th(1) != 1001) { return 6; }
    sk: fn(long) -> long = &skips;
    if (sk(10) != 1 + 2 + 3 - 1 + 5 + 6 + 7 - 1 + 9 + 10 || sk(0) != 0) { return 7; }
    wr: fn(u8) -> long = &wraps;
    if (wr(250) != 6005 || wr(5) != 0 || wr(4) != 1000) { return 8; }
    fp: fn([long], long) -> long = &findPair;
    xs: [long; 5] = [4, -1, 9, 3, 6];
    if (fp(xs[..], 9) != 304 || fp(xs[..], 100) != -1 || fp(xs[..], 3) != 1) { return 9; }
    li: fn(long) -> long = &lastIndex;
    if (li(0) != 0 || li(10) != 4 || li(1000) != 50) { return 10; }
    fg: fn(long) -> long = &flagLoop;
    if (fg(0) != 0 || fg(3) != 3) { return 11; }
    pk: fn(long) -> long = &pick;
    pf: fn(bool) -> long = &pickFlag;
    pd: fn(f64) -> long = &pickFloat;
    zero: f64 = 0.0;
    if (pk(4) != 1 || pk(3) != 2 || pf(true) != 1 || pf(false) != 2) { return 12; }
    if (pd(0.5) != 1 || pd(2.0) != 2 || pd(zero / zero) != 2) { return 13; }
    return 0;
}
