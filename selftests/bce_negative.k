// A loop that starts below zero: `i < v.len()` holds, `i >= 0` does not, and the first read
// must panic.
#include <stdlib::vec>
main -> int {
    v: Vec<long>;
    for i in 0..4 { v.push(i); }
    s: long = 0;
    i: long = -1;
    while (i < v.len()) { s = s + v.get(i); i = i + 1; }
    return s as int;
}
