// Nor can a value declared without one be built field by field when it owns two fields: the one
// not yet stored would be released at the scope's end, holding nothing.
#include <stdlib::core>
struct Res { id: long }
methods Res for Drop { drop &self -> void { } }
struct Acc { s: Res, t: Res }
main -> int {
    acc: Acc;
    acc.s = Res { id: 100 };
    return 0;
}
