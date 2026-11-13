// An arm of `match &x.f` holds a borrow of the payload, so writing `x.f` there is refused.
#include <stdlib::core>
struct Res { n: long }
methods Res for Drop { drop &self -> void { } }
enum K { A(Res), B }
struct S { k: K }
main -> int {
    x: S = S { k: K.A(Res { n: 5 }) };
    match &x.k { A(r) { x.k = K.B; return r.n as int; } B { } }
    return 0;
}
