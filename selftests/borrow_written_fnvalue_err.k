// Two lends of one value through a fn value, whose function writes through one of them: a `&T`
// the callee writes through is held to the law of exclusivity as an `inout` lend is, and a call
// through a fn value is held to what every function the value may hold does.
#include <stdlib::vec>
f a:&Vec<long> b:&Vec<long> -> long { n: long = b.len(); a.pop(); return n * 10 + b.len(); }
main -> int {
    v: Vec<long> = vec![1, 2, 3];
    ff: fn(&Vec<long>, &Vec<long>) -> long = &f;
    return ff(&v, &v) as int;
}
