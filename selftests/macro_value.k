// A `macro` returning a value: run by the compiler at every call, the call replaced by the
// result. `square!(7)` is the literal 49 by the time the lowerer sees it; an argument must be
// something the compiler can compute. Exit code: 49 + 8 + 6.
macro square x:long -> long { return x * x; }
macro fib n:long -> long { if (n < 2) { return n; } return fib(n - 1) + fib(n - 2); }
macro three -> long { return 1 + 2 + 3; }

main -> int { return (square!(7) + fib!(6) + three!()) as int; }
