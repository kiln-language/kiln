// The index moves between the loop's own test and the read: `i < v.len()` says nothing about
// `i + 1`, so the second read keeps its check and panics on an odd length.
#include <stdlib::vec>
main -> int {
    v: Vec<long>;
    for i in 0..5 { v.push(i); }
    i: long = 0;
    s: long = 0;
    while (i < v.len()) {
        s = s + v.get(i);
        i = i + 1;
        s = s + v.get(i);
        i = i + 1;
    }
    return s as int;
}
