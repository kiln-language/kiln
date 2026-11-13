// One run reports the first error of every function, not only of the first, and says how many.
#include <stdlib::string>
struct P { x: long }
one -> long { s: String = stringOf("a"); return s.nosuch(); }
two -> long { p: P = P { x: 1 }; return p.nosuch; }
three -> long { n: long = "text"; return n; }
main -> int { return (one() + two() + three()) as int; }
