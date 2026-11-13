// A call through a fn value cannot write a scalar or a `str` it is handed (each crosses as a
// copy, and a str's bytes are never written), so an immutable global of either type may be
// passed through one, and so may a `for x in xs` element or a read-only parameter.
#include <stdlib::vec>
G: str = "global";
N: long = 40;
cnt s:str -> long { return s.len; }
inc x:long -> long { return x + 1; }
apply f:fn(str)->long s:str -> long { return f(s) + f(s); }
sumWith f:fn(long)->long xs:Vec<long> -> long { t: long = 0; for x in xs { t = t + f(x); } return t; }
main -> int {
    f: fn(str)->long = &cnt;
    g: fn(long)->long = &inc;
    xs: Vec<long>; xs.push(1); xs.push(2);
    n: long = f(G) + g(N) + apply(&cnt, G) + sumWith(&inc, xs);   // 6 + 41 + 12 + 5
    if (n != 64) { return 1; }
    return 0;
}
