// `_ = value;` evaluates and releases what it yields at once; `_` as a destructuring target
// discards that element (released at once too). A `MustUse` result discarded this way is fine.
#include <stdlib::{core, result}>
var drops: long = 0;
struct R { id: long }
methods R for Drop { drop &self -> void { drops = drops + self.id; } }
mk id:long -> R { return R { id: id }; }
pair -> (R, R) { return (mk(1), mk(10)); }
fails -> Result<long, long> { return Result.Err(3); }
noisy -> long { drops = drops + 5; return 7; }
main -> int {
    _ = mk(100);                       // released here
    if (drops != 100) { return 1; }
    _ = fails();                       // MustUse, dropped on purpose
    _ = noisy();                       // evaluated: 105
    keep: R = mk(1000);
    _ = keep;                          // a place: read, nothing moved or released
    a, _ = pair();                     // the 10 released here: 115
    if (drops != 115) { return 2; }
    y: R = mk(0);
    _, y = pair();                     // y assigned (its 0 released), the 1 released: 116
    _, _ = pair();                     // both released: 127
    t: (long, R) = (4, mk(0));
    n, _ = t;                          // the R taken out of t and released; t gives the rest
    return (drops - 100 + n + keep.id / 1000 + a.id + y.id) as int;   // 27 + 4 + 1 + 1 + 10 = 43
}
