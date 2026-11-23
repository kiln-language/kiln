// The same index read twice is checked once, unless it moved in between. Here it moved past
// the end, and the second read must panic.
#include <stdlib::vec>
main -> int {
    v: Vec<long>;
    for i in 0..3 { v.push(i); }
    h: long = 2;
    a: long = v.get(h);
    h = h + 1;
    b: long = v.get(h);
    return (a + b) as int;
}
