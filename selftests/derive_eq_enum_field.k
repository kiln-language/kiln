// Derived `==` where a field is a backed enum: equal, and unequal for each field in turn.
#include <stdlib::io>

enum Color: int { Red, Green, Blue }
enum Small: u8 { A, B }

struct WithEnum { c: Color, n: long }
struct TwoEnums { c: Color, s: Small }
struct Nested { w: WithEnum, k: long }

main -> int {
    a: WithEnum = WithEnum { c: Color.Red,   n: 1 };
    b: WithEnum = WithEnum { c: Color.Red,   n: 1 };
    d: WithEnum = WithEnum { c: Color.Green, n: 1 };   // the enum field differs
    e: WithEnum = WithEnum { c: Color.Red,   n: 2 };   // the scalar field differs
    println("same={} enumDiffers={} scalarDiffers={}", a == b, a == d, a == e);

    t1: TwoEnums = TwoEnums { c: Color.Blue, s: Small.B };
    t2: TwoEnums = TwoEnums { c: Color.Blue, s: Small.B };
    t3: TwoEnums = TwoEnums { c: Color.Blue, s: Small.A };   // a u8-backed enum differs
    println("twoEnums same={} differs={}", t1 == t2, t1 == t3);

    n1: Nested = Nested { w: a, k: 3 };
    n2: Nested = Nested { w: d, k: 3 };
    n3: Nested = Nested { w: b, k: 3 };
    println("nested same={} differs={}", n1 == n3, n1 == n2);

    // 1 + 0 + 0 + 1 + 0 + 1 + 0 = 3 trues
    n: long = 0;
    if (a == b) { n = n + 1; }
    if (t1 == t2) { n = n + 1; }
    if (n1 == n3) { n = n + 1; }
    if (a == d) { n = n + 10; }
    if (a == e) { n = n + 10; }
    if (t1 == t3) { n = n + 10; }
    if (n1 == n2) { n = n + 10; }
    return n as int;
}
