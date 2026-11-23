// An address made once, before a loop or in another block, joins each access through it
// (`Flow.foldAddressesWide`): the loop reads `self.b`'s buffer and count at their offsets from
// `self`, and no register holds `&self.b` through it.
// ir-lacks: wide_addr::Two_sumB , #24
#include <stdlib::vec>
struct Two { a: Vec<long>, b: Vec<long> }
methods Two {
    sumB &self -> long {
        s: long = 0;
        for i in 0..self.b.len() { s = s + self.b.get(i) * self.a.len(); }
        return s;
    }
}
main -> int {
    t: Two = Two { a: vec![], b: vec![] };
    t.a.push(1); t.a.push(2);
    for i in 0..5 { t.b.push(i); }
    if (t.sumB() != 20) { return 1; }
    return 0;
}
