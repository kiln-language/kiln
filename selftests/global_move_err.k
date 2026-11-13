// A global holding an owning value cannot be moved out: it keeps naming the value, so whatever
// took it releases memory the global still points at (the use-after-free behind the crash a
// synthesized `@init` runner hit: `hooks: Vec<Sym> = gInitHooks;`). Each function is refused.
#include <stdlib::vec>
var gL: Vec<long> = vec![];
G: Vec<long> = vec![1, 2];
struct Holder { items: Vec<long> }
toLocal -> long { h: Vec<long> = gL; return h.len(); }
toLocalConst -> long { h: Vec<long> = G; return h.len(); }
sinkIt v:Vec<long> -> long { return v.len(); }
toSink -> long { return sinkIt(gL); }
give -> Vec<long> { return gL; }
toLiteral -> long { h: Holder = Holder { items: gL }; return h.items.len(); }
reassign -> long { h: Vec<long> = vec![]; h = gL; return h.len(); }
main -> long { return toLocal() + toLocalConst() + toSink() + give().len() + toLiteral() + reassign(); }
