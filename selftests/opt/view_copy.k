// `s.startsWith("key=")` over a `String`: the view the method builds is the pair the inlined test
// reads, with no copy of it into an argument slot, the literal's length is the constant 4, and
// the `bool` the inlined body returned is a branch on the comparison it came from. No block copy
// is left: the `String` is made in `s` (`buildWhereCopied`). In the loop, `bytesEqual` with the
// four-byte literal is copied in for what that length leaves of it (`foldTarget`), and the
// literal's bytes are one constant.
// ir-lacks: main aggcopy
// ir-lacks: main bounds
// ir-lacks: main = cmpeq
// ir-lacks: main call bytes::bytesEqual
// ir-has: main #1031365995
#include <stdlib::string>
main -> int {
    s: String;
    s.pushStr("key=value");
    n: long = 0;
    for i in 0..3 { if (s.startsWith("key=")) { n += 1; } }
    return (n - 3) as int;
}
