// A local the macro's code declares gets a name of its own at every splice, so two uses in one
// scope do not collide and the macro's `tmp` never captures the caller's `tmp`. Exit code:
// 10 + 20 + 7 = 37.
#include <stdlib::ast>
#include <stdlib::heap>
#include <stdlib::vec>

// `twice!(e)`: evaluates `e` once into a temporary and yields its double, as a block.
macro twice e:Node -> Node {
    return quote { tmp: long = @e; total = total + tmp + tmp; };
}

var total: long = 0;
main -> int {
    tmp: long = 7;                 // the caller's tmp: untouched by the macro's
    twice!(5);
    twice!(10);
    return (total + tmp) as int;
}
