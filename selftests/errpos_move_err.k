// The ownership walk reports where the moved value is read again.
#include <stdlib::io>
struct Res { n: long }
methods Res for Drop { drop &self -> void { } }
take sink r:Res -> long { return r.n; }
main -> int {
    r: Res = Res { n: 1 };
    a: long = take(r);
    if (a > 0) {
        println("{}", r.n);
    }
    return 0;
}
