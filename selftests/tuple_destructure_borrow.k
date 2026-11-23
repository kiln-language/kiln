// A tuple that owns something, taken apart through a reference (`v.at(0)`), is taken apart as a
// borrowed tuple is: its names are borrows of its elements, nothing is moved out of the vector, and
// each element is released once, by the vector. Exits with the number of the first check that fails.
#include <stdlib::vec>
var gDrops: long = 0;
struct Res { id: long, n: long }
methods Res for Drop { drop &self -> void { gDrops = gDrops + self.id; } }
run -> long {
    v: Vec<(long, Res)>;
    v.push((1, Res { id: 10, n: 0 }));
    c, d = v.at(0);
    d.n = 7;
    return c * 100 + v.at(0).1.n;
}
main -> int {
    if (run() != 107) { return 1; }
    if (gDrops != 10) { return 2; }
    return 0;
}
