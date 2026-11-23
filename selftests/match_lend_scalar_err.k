// Lending a scalar binding to an `inout` parameter would assign it as a whole.
enum E { Num(long), Other }
bump inout n:long -> void { n = n + 1; }
inc inout e:E -> void { match e { Num(q) { bump(&q); } _ { } } }
main -> int { a: E = E.Num(1); inc(&a); return 0; }
