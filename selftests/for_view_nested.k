// A `for` over a type implementing `AsSlice<T>` may walk the same collection again inside: the
// inner loop's `asSlice` call reads it (`&self` that writes nothing), and its slice local is the
// loop's own. So may it walk a collection inside the element it has (Ember's
// `for cp in c.kids { for s in cp.kids { ... } }`). A write inside either is still refused
// (`for_view_err`).
#include <stdlib::vec>
struct Bag { items: Vec<long> }
methods Bag for AsSlice<long> {
    asSlice &self -> [long] { unsafe { return self.items.buf.ptr[..self.items.count]; } }
}
struct Row { vals: Vec<long> }
struct Table { rows: Vec<Row> }
total t:&Table -> long {
    s: long = 0;
    for r in t.rows { for x in r.vals { s = s + x; } }
    return s;
}
main -> long {
    v: Vec<long> = vec![1, 2, 3, 4];
    pairs: long = 0;
    for a in v { for b in v { if (a < b) { pairs = pairs + 1; } } }
    g: Bag = Bag { items: vec![5, 1, 9] };
    over: long = 0;
    for a in g { for b in g { if (a > b) { over = over + a - b; } } }
    t: Table = Table { rows: vec![] };
    t.rows.push(Row { vals: vec![1, 2] });
    t.rows.push(Row { vals: vec![3] });
    if (total(&t) != 6) { return 1; }
    return pairs * 10 + over;
}
