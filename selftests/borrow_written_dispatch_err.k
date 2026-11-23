// A dispatch is held to what every implementation does: one that writes through its `&T`
// parameter makes that lend exclusive, so the same vector cannot also be the other argument.
#include <stdlib::vec>
trait Merge { merge &self into:&Vec<long> from:&Vec<long> -> void; }
struct Append { k: long }
struct Count { k: long }
methods Append for Merge { merge &self into:&Vec<long> from:&Vec<long> -> void { into.push(from.len()); } }
methods Count for Merge { merge &self into:&Vec<long> from:&Vec<long> -> void { } }
run m:Merge v:&Vec<long> -> void { m.merge(v, v); }
main -> int {
    v: Vec<long> = vec![1, 2];
    a: Append = Append { k: 0 };
    run(a, &v);
    return v.len() as int;
}
