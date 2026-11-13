// `~a` on a type of your own is a call to its `Not`. It used to fall through to the machine
// operation on the pointer an aggregate flows as: `~s` complemented the ADDRESS and handed the
// result back typed as the struct, with no diagnostic.
//
// Exit code: ~5 is -6, and ~(-6) is 5, so 5 + 0 = 5.
#include <stdlib::io>

struct M { b: long }
methods M for Not { not self -> M { return M { b: ~self.b }; } }

main -> int {
    x: M = ~M { b: 5 };
    y: M = ~x;
    println("once={} twice={}", x.b, y.b);
    if (x.b != 0 - 6) { return 90; }
    return y.b as int;
}
