// A local of a struct type with no Default, declared without a value, holds stack garbage. Lending
// one of its fields `inout` hands that garbage to a callee that may read it (here: swap it into a
// live value, which is then released twice). Refused as reading the local would be.
#include <stdlib::{core, vec, mem}>
struct R { id: long }
methods R for Drop { drop &self -> void { } }
struct A { r: R, n: long }
struct H { pending: R, list: Vec<A> }
methods H {
    commit &self -> void {
        a: A;
        swapValues(&a.r, &self.pending);
        self.list.push(a);
    }
}
main -> int {
    h: H = H { pending: R { id: 1 } };
    h.commit();
    return 0;
}
