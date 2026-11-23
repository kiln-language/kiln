#include <stdlib::vec>
// `v[..]` on a Vec is no slice of its elements.
sum xs:[long] -> long { t: long = 0; for x in xs { t = t + x; } return t; }
main -> long { v: Vec<long> = vec![1, 2, 3]; return sum(v[..]); }
