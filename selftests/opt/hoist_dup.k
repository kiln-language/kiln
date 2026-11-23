// One load hoisted out of a loop twice, by two copies of one inlined body, is made once
// (`Flow.sameHoisted`): `count` reads `self.uses`' count and buffer in each of its two calls of
// `note`, and each pair is one load before the loop.
// ir-count: hoist_dup::Counts_count ptrload [t0 + 16] 1
// ir-count: hoist_dup::Counts_count ptrload [t0] 1
#include <stdlib::vec>
struct Counts { uses: Vec<long> }
methods Counts {
    note &self t:long -> void {
        if (t < 0 || t >= self.uses.len()) { return; }
        self.uses.set(t, self.uses.get(t) + 1);
    }
    count &self xs:&Vec<long> -> void {
        for x in xs { self.note(x); self.note(x + 1); }
    }
}
main -> int {
    c: Counts = Counts { uses: vec![] };
    for i in 0..8 { c.uses.push(0); }
    xs: Vec<long>;
    for i in 0..8 { xs.push(i); }
    c.count(&xs);
    if (c.uses[0] != 1 || c.uses[3] != 2 || c.uses[7] != 2) { return 1; }
    return 0;
}
