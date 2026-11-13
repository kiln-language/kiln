// A value moved away whole cannot be brought back one field at a time when it owns more than
// that field: the others would come back holding what was moved (a double release).
#include <stdlib::core>
struct Res { id: long }
methods Res for Drop { drop &self -> void { } }
struct Acc { s: Res, t: Res }
eat sink a:Acc -> long { return a.s.id; }
main -> int {
    acc: Acc = Acc { s: Res { id: 1 }, t: Res { id: 2 } };
    eat(acc);
    acc.s = Res { id: 10 };
    return 0;
}
