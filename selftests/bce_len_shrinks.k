// The length captured before the loop goes stale when the body pops: the check must stay, and
// the read past the new end must panic (134), not read the slot the pop left behind.
#include <stdlib::vec>
main -> int {
    v: Vec<long>;
    for i in 0..8 { v.push(i); }
    n: long = v.len();
    s: long = 0;
    for i in 0..n {
        v.pop();
        s = s + v.get(i);
    }
    return s as int;
}
