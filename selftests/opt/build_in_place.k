// A value is built where it is copied to: a struct literal in the local it initializes, an
// inlined callee's returned local in the caller's, and a literal returned from a function in the
// caller's memory (`flow.k` `buildWhereCopied`). A literal that reads what it replaces keeps its
// scratch and the copy.
// ir-lacks: build_in_place::fresh aggcopy
// ir-lacks: build_in_place::viaCallee aggcopy
// ir-lacks: build_in_place::make aggcopy
// ir-has: build_in_place::bump aggcopy
#include <stdlib::{vec}>
struct Tree { items: Vec<long>, count: long, tag: long }
var gSeen: long = 0;
look t:&Tree -> long { gSeen = gSeen + 1; return t.items.len() + t.count + t.tag; }
fresh n:long -> long {
    t: Tree = Tree { items: vec![n, n], count: 1, tag: n };
    return look(&t);
}
grown n:long -> Tree {
    t: Tree = Tree { items: vec![], count: 0, tag: 7 };
    t.items.push(n);
    t.count = n;
    return t;
}
viaCallee n:long -> long {
    t: Tree = grown(n);
    return look(&t);
}
make n:long -> Tree { return Tree { items: vec![n], count: n, tag: n * 2 }; }
bump n:long -> long {
    t: Tree = make(n);
    s: Tree = Tree { items: vec![], count: t.count + 1, tag: look(&t) };
    t = Tree { items: vec![1], count: s.count + t.count, tag: s.tag };
    return look(&t);
}
main -> int {
    if (fresh(3) != 6) { return 1; }
    if (viaCallee(5) != 13) { return 2; }
    m: Tree = make(4);
    if (look(&m) != 13) { return 3; }
    if (bump(2) != 13) { return 4; }
    return 0;
}
