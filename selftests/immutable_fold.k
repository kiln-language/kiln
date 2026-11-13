// A global is immutable by default: computed by the compiler, read-only ever after, in `.rodata`.
// table of squares, both built by loops at compile time; reads through methods the guard proved
// do not write (`get`, `len`). The exit code is PRIMES[4] + SQ[7] + N = 11 + 49 + 3.
#include <stdlib::vec>

sieve n:long -> Vec<long> {
    v: Vec<long>;
    i: long = 2;
    while (i <= n) {
        p: bool = true;
        j: long = 2;
        while (j * j <= i) { if (i % j == 0) { p = false; } j = j + 1; }
        if (p) { v.push(i); }
        i = i + 1;
    }
    return v;
}
struct Squares { sq: [long; 10] }
squares -> Squares {
    s: Squares = Squares { };
    i: long = 0;
    while (i < 10) { s.sq[i] = i * i; i = i + 1; }
    return s;
}

PRIMES: Vec<long> = sieve(30);
SQ: Squares = squares();
N: long = 1 + 2;

main -> int { return (PRIMES.get(4) + SQ.sq[7] + N + PRIMES.len() - PRIMES.len()) as int; }
