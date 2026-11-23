// A trait method that takes a parameter `inout`, reached through a trait object: the lend is
// held to the law of exclusivity as a direct call's is, so `v` cannot also be the other argument.
#include <stdlib::vec>
trait Merge { merge &self inout into:Vec<long> from:&Vec<long> -> void; }
struct Append { k: long }
methods Append for Merge { merge &self inout into:Vec<long> from:&Vec<long> -> void { into.push(from.len()); } }
run m:Merge v:&Vec<long> -> void { m.merge(&v, v); }
main -> int {
    v: Vec<long> = vec![1, 2];
    a: Append = Append { k: 0 };
    run(a, &v);
    return v.len() as int;
}
