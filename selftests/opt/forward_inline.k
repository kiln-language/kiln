// A body that only hands its call on (`Relayout.forwardingBody`) is copied to every call site
// with its callee: reading one field of what `Pool.item` returns calls nothing, and the item is
// copied once at most (each copy has scratch slots of its own, `spliceInstr`, so two items live
// at once, as `pair` passes them, are two).
// ir-lacks: forward_inline::firsts call vec::
// ir-lacks: forward_inline::lasts call vec::
#include <stdlib::vec>
struct Item { a: long, b: long, c: long, d: long, e: long }
struct Pool { items: Vec<Item> }
methods Pool {
    item &self i:long -> Item { return self.items.get(i); }
}
firsts p:&Pool -> long { return p.item(0).a + p.item(1).b + p.item(2).c; }
lasts p:&Pool -> long { return p.item(2).e + p.item(1).d; }
both x:Item y:Item -> long { return x.a * 1000 + y.a * 100 + x.e * 10 + y.e; }
pair p:&Pool -> long { return both(p.item(1), p.item(2)); }
main -> int {
    p: Pool = Pool { items: vec![] };
    for i in 0..3 { p.items.push(Item { a: i, b: i * 10, c: i * 100, d: i + 1, e: i + 2 }); }
    if (firsts(&p) != 210) { return 1; }
    if (lasts(&p) != 6) { return 2; }
    if (pair(&p) != 1234) { return 3; }
    return 0;
}
