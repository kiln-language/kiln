// A borrow lives across the call that makes it and no longer. Held in a local it outlives that,
// and the next push may move the block it points into.
#include <stdlib::vec>
struct Res { id: long }
main -> int {
    v: Vec<Res>; v.push(Res { id: 1 });
    p: &Res = v.at(0);
    v.push(Res { id: 2 });
    return p.id as int;
}
