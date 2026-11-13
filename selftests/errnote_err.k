// An error inside a generic instance says where the instance was asked for, link by link back to
// code nothing stamped: `W<long>` (asked for in main) calls `outer<long>`, which calls
// `inner<long>`, whose body is wrong for `long`.
inner<T> x:T -> long { s: str = x; return 0; }
outer<T> x:T -> long { return inner(x); }
struct W<T> { v: T }
methods W<T> { run &self -> long { return outer(self.v); } }
main -> int {
    w: W<long> = W { v: 3 };
    return w.run() as int;
}
