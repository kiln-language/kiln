// `for x in G` over a global another module declares: the element type is read through the
// includes, as the name itself is. Scalars, struct elements, the lending form, a field of one.
// Exit code 3 + 12 + 4 + 10 = 29.
#include <stdlib::vec>
#include <tables>

main -> int {
    fill();
    s: long = 0;
    for x in gItems { s = s + x; }
    for p in gPts { s = s + p.x * p.y; }
    for p in &gPts { p.x = p.x + 1; }
    for p in gPts { s = s + p.x; }
    for x in gBag.items { s = s + x; }
    return s as int;
}
