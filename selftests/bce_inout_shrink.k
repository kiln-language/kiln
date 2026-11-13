// The vector is lent `inout` to a function that shrinks it, inside a loop whose bound was read
// before the loop: the read after the call keeps its check, and fails it at i = 3.
#include <stdlib::vec>
shrink inout v:Vec<long> -> void { v.truncate(v.len() - 1); }
main -> int {
    v: Vec<long>;
    for i in 0..6 { v.push(i); }
    n: long = v.len();
    s: long = 0;
    for i in 0..n {
        shrink(&v);
        s = s + v.get(i);
    }
    return s as int;
}
