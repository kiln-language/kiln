#include <stdlib::{io, vec}>

// A closure that reads and writes an `inout` struct parameter, through a generic `Fn` bound and
// through a trait-object `Fn` parameter. The parameter is a borrow of the caller's value, and the
// closure holds that borrow.

viaBound<F: Fn() -> void> f:F -> void { f(); }
viaObj f:Fn() -> void -> void { f(); }

struct Tree { items: Vec<long>, count: long }

growBound inout t:Tree v:long -> void { viaBound(|| { t.items.push(v); t.count = t.count + 1; }); }
growObj inout t:Tree v:long -> void { viaObj(|| { t.items.push(v); t.count = t.count + 1; }); }
lenBound inout t:Tree -> long { n: long = 0; viaBound(|| { n = t.items.len() + t.count; }); return n; }
lenObj inout t:Tree -> long { n: long = 0; viaObj(|| { n = t.items.len() + t.count; }); return n; }
// handed on from inside the closure, as `inout` again
growTwice inout t:Tree -> void { viaObj(|| { growBound(&t, 1); growObj(&t, 2); }); }

main -> long {
    t: Tree = Tree { items: vec![], count: 0 };
    growBound(&t, 7);
    growObj(&t, 8);
    if (t.items.len() != 2 || t.count != 2) { return 1; }
    if (t.items[0] != 7 || t.items[1] != 8) { return 2; }
    if (lenBound(&t) != 4 || lenObj(&t) != 4) { return 3; }
    growTwice(&t);
    if (t.items.len() != 4 || t.count != 4 || t.items[3] != 2) { return 4; }
    return 0;
}
