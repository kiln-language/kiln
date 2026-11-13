// Inside `unsafe`, `&a.r` handed to an `inout` parameter is still a lend the callee may read;
// only a raw address (`&a as long`) is trusted code's to fill.
#include <stdlib::{core, mem}>
struct R { id: long }
methods R for Drop { drop &self -> void { } }
struct A { r: R, n: long }
main -> int {
    keep: R = R { id: 3 };
    a: A;
    unsafe { swapValues(&a.r, &keep); }
    a.n = 0;
    return 0;
}
