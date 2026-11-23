// A call whose result its caller only combines with a value and returns, `return x op f(...)`,
// becomes an accumulator and a jump back (`Relayout.accOf`), for each operator that wrapping keeps
// associative and commutative: `fib`'s second call is a loop and its first stays a call. The
// shapes that must stay calls: two operators in one function, a result combined with itself, a
// subtraction, floats, a local with a destructor live at the return, a `recover`, and an operand
// with side effects worked out after the call. One worked out before it keeps its order.
// ir-count: accumulate::fib call accumulate::fib 1
// ir-count: accumulate::sumTo call accumulate::sumTo 0
// ir-count: accumulate::fact call accumulate::fact 0
// ir-count: accumulate::count call accumulate::count 0
// ir-count: accumulate::mix call accumulate::mix 0
// ir-count: accumulate::andDown call accumulate::andDown 0
// ir-count: accumulate::orUp call accumulate::orUp 0
// ir-count: accumulate::sumInt call accumulate::sumInt 0
// ir-count: accumulate::mixed call accumulate::mixed 2
// ir-count: accumulate::selfTwice call accumulate::selfTwice 1
// ir-count: accumulate::minus call accumulate::minus 1
// ir-count: accumulate::fsum call accumulate::fsum 1
// ir-count: accumulate::withDrop call accumulate::withDrop 1
// ir-count: accumulate::withRecover call accumulate::withRecover 1
// ir-count: accumulate::before call accumulate::before 0
// ir-count: accumulate::after call accumulate::after 1
#include <stdlib::recover>

var gDrops: long = 0;
var gLog: long = 0;

struct Tok { n: long }
methods Tok for Drop { drop &self -> void { gDrops = gDrops * 3 + self.n; } }

// Each frame's `t` is dropped as that frame returns, after the call inside it: innermost first.
withDrop n:long -> long {
    if (n == 0) { return 0; }
    t: Tok = Tok { n: n };
    return t.n + withDrop(n - 1);
}
withRecover n:long -> long {
    if (n == 0) { return 0; }
    r: long = 0;
    unsafe { recover { if (n == 3) { raise(); } r = 1; } else { r = 100; } }
    return r + withRecover(n - 1);
}
note k:long -> long { gLog = gLog * 7 + k; return k; }
before n:long -> long {
    if (n == 0) { return 0; }
    return note(n) + before(n - 1);
}
after n:long -> long {
    if (n == 0) { return 0; }
    return after(n - 1) + note(n);
}

fib n:long -> long {
    if (n < 2) { return n; }
    return fib(n - 1) + fib(n - 2);
}
sumTo n:long -> long {
    if (n == 0) { return 0; }
    return n + sumTo(n - 1);
}
fact n:long -> long {
    if (n <= 1) { return 1; }
    return n * fact(n - 1);
}
count n:long -> long {
    if (n == 0) { return 0; }
    return count(n - 1) + 1;
}
mix n:long -> long {
    if (n == 0) { return 7; }
    return (n * 2654435761) ^ mix(n - 1);
}
andDown n:long -> long {
    if (n == 0) { return -1; }
    return andDown(n - 1) & (n | 1);
}
orUp n:long -> long {
    if (n == 0) { return 0; }
    return (1 << (n % 64)) | orUp(n - 1);
}
// Wraps at 32 bits as the loop below does.
sumInt n:int -> int {
    if (n == 0) { return 0; }
    return n * 100000 + sumInt(n - 1);
}
mixed n:long -> long {
    if (n < 2) { return n; }
    if (n % 2 == 0) { return mixed(n - 1) + 3; }
    return mixed(n - 1) * 3;
}
selfTwice n:long -> long {
    if (n == 0) { return 1; }
    t: long = selfTwice(n - 1);
    return t + t;
}
minus n:long -> long {
    if (n == 0) { return 0; }
    return n - minus(n - 1);
}
fsum n:long -> f64 {
    if (n == 0) { return 0.0; }
    return 1.5 + fsum(n - 1);
}

main -> int {
    a: long = 0; b: long = 1;
    for i in 0..30 { c: long = a + b; a = b; b = c; }
    if (fib(30) != a) { return 1; }
    if (sumTo(100000) != 5000050000) { return 2; }
    f: long = 1;
    for i in 1..26 { f = f * i; }
    if (fact(25) != f) { return 3; }
    if (count(100000) != 100000) { return 4; }
    m: long = 7;
    for i in 1..1001 { m = m ^ (i * 2654435761); }
    if (mix(1000) != m) { return 5; }
    d: long = -1;
    for i in 1..101 { d = d & (i | 1); }
    if (andDown(100) != d) { return 6; }
    o: long = 0;
    for i in 1..71 { o = o | (1 << (i % 64)); }
    if (orUp(70) != o) { return 7; }
    s: int = 0;
    for i in 1..50001 { s = s + (i as int) * 100000; }
    if (sumInt(50000) != s) { return 8; }
    if (mixed(6) != 48) { return 9; }
    if (selfTwice(10) != 1024) { return 10; }
    if (minus(5) != 3) { return 11; }
    if (fsum(4) != 6.0) { return 12; }
    if (withDrop(5) != 15) { return 13; }
    dr: long = 0;
    for k in 1..6 { dr = dr * 3 + k; }
    if (gDrops != dr) { return 14; }
    if (withRecover(5) != 104) { return 15; }
    if (before(5) != 15) { return 16; }
    lg: long = 0;
    for k in 0..5 { lg = lg * 7 + (5 - k); }
    if (gLog != lg) { return 17; }
    gLog = 0;
    if (after(5) != 15) { return 18; }
    la: long = 0;
    for k in 1..6 { la = la * 7 + k; }
    if (gLog != la) { return 19; }
    return 0;
}
