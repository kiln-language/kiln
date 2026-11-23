#include <stdlib::{io, vec}>

// A closure inside a `&self` method that reads and writes `self`, through a generic `Fn` bound
// and through a trait-object `Fn` parameter. `self` is a borrow: the closure holds that borrow,
// and a write through it lands on the caller's value.

viaBound<F: Fn() -> void> f:F -> void { f(); }
viaObj f:Fn() -> void -> void { f(); }

struct Counter { seen: long, items: Vec<long> }
methods Counter {
    readBound &self -> long { n: long = 0; viaBound(|| { n = self.seen; }); return n; }
    readObj &self -> long { n: long = 0; viaObj(|| { n = self.seen; }); return n; }
    bumpBound &self by:long -> void { viaBound(|| { self.seen = self.seen + by; self.items.push(self.seen); }); }
    bumpObj &self by:long -> void { viaObj(|| { self.seen = self.seen + by; self.items.push(self.seen); }); }
    // a closure inside a closure: the inner one reaches `self` through the outer one's capture
    nested &self -> long {
        n: long = 0;
        viaBound(|| { viaObj(|| { n = self.seen * 2; self.seen = 1; }); });
        return n;
    }
    total &self -> long {
        s: long = 0;
        viaObj(|| { i: long = 0; while (i < self.items.len()) { s = s + self.items[i]; i = i + 1; } });
        return s;
    }
}

// The same in a generic type's methods, where `self` names the template.
struct Pair<T> { a: T, b: T }
methods Pair<T> {
    swapIn &self -> void { viaObj(|| { t: T = self.a; self.a = self.b; self.b = t; }); }
    second &self -> T { r: T = self.a; viaBound(|| { r = self.b; }); return r; }
}

main -> long {
    c: Counter = Counter { seen: 6, items: vec![] };
    if (c.readBound() != 6) { return 1; }
    if (c.readObj() != 6) { return 2; }
    c.bumpBound(3);
    if (c.seen != 9 || c.items.len() != 1) { return 3; }
    c.bumpObj(5);
    if (c.seen != 14 || c.items.len() != 2) { return 4; }
    if (c.total() != 23) { return 5; }
    if (c.nested() != 28 || c.seen != 1) { return 6; }
    p: Pair<long> = Pair { a: 3, b: 4 };
    p.swapIn();
    if (p.a != 4 || p.b != 3) { return 7; }
    if (p.second() != 3) { return 8; }
    return 0;
}
