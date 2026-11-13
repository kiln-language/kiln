// A `for` body that changes the walked `var` global through a function that names it: the loop
// reads the elements where they lie, and `refill` may move them.
#include <stdlib::vec>
var gItems: Vec<long> = vec![1, 2, 3];
refill -> void { gItems.push(4); }
main -> int {
    t: long = 0;
    for x in gItems { t = t + x; refill(); }
    return t as int;
}
