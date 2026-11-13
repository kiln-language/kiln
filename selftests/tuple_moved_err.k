// After `a, b = t;` the tuple's elements belong to `a` and `b`: reading one through `t` is a use
// of a moved value.
#include <stdlib::core>
struct Res { n: long }
methods Res for Drop { drop &self -> void { } }
mk -> (Res, long) { return (Res { n: 1 }, 2); }
main -> int {
    t: (Res, long) = mk();
    a, b = t;
    return t.0.n as int;
}
