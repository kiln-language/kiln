// `<` `>` `<=` `>=` on a struct dispatch to its `Ord`, as `a.cmp(b) <op> 0`.
//
// They used to fall through to the machine compare, and an aggregate flows as a pointer, so two
// structs with identical fields reported an order and which came first depended on where they sat
// in the frame. `p` and `q` below are the case that showed it: same contents, and `p > q` was true.
//
// Exit code: 6 correct answers.
#include <stdlib::io>
#include <stdlib::cmp>

struct V { x: long }
methods V for Ord { cmp &self other:V -> int { return (self.x - other.x) as int; } }

main -> int {
    lo: V = V { x: 1 };
    hi: V = V { x: 900 };
    p: V = V { x: 5 };
    q: V = V { x: 5 };

    n: long = 0;
    if (lo < hi)  { n = n + 1; }        // true
    if (hi > lo)  { n = n + 1; }        // true
    if (lo <= hi) { n = n + 1; }        // true
    if (p <= q)   { n = n + 1; }        // equal, so true
    if (p >= q)   { n = n + 1; }        // equal, so true
    if (!(p < q)) { n = n + 1; }        // equal, so NOT less: the address compare got this wrong
    if (hi < lo)  { n = n + 100; }      // must not fire
    if (p > q)    { n = n + 100; }      // must not fire
    println("ordered answers: {}", n);
    return n as int;
}
