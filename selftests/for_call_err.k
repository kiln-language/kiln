// `for x in` reads its collection's type where it is named: a call's result is bound first.
#include <stdlib::vec>
mk -> Vec<long> { v: Vec<long>; v.push(1); return v; }
main -> int { n: long = 0; for x in mk() { n = n + x; } return n as int; }
