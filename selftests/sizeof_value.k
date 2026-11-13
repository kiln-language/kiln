// `sizeof(T)` is a long wherever it stands: handed to a `...any` run (it was boxed as a T, and a
// T with Display was formatted from the count's bytes), cast, compared, and stored, including
// with T a generic instance and inside a generic body.
#include <stdlib::io>
#include <stdlib::fmt>
#include <stdlib::string>
#include <stdlib::fixedstring>

struct P { x: long }
methods P for Display { display &self w:Write -> void { writeTo(w, "P({})", self.x); } }
struct Q<T> { a: T, b: T }
twice<T> x:T -> long { return sizeof(T) * 2; }

main -> int {
    s: String = format("{}", sizeof(P));
    if (s != "8") { return 1; }
    t: String = format("{} {}", sizeof(Q<P>), sizeof(FixedString<8>));
    if (t != "16 24") { return 2; }
    k: int = sizeof(P) as int;
    if (k != 8 || sizeof(P) != 8 || sizeof(P) == 9) { return 3; }
    n: long = sizeof(P) + 1;
    if (n != 9 || twice(P { x: 1 }) != 16) { return 4; }
    println("sizeof(P) = {}", sizeof(P));
    return 0;
}
