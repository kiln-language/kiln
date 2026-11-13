// `for x in G` over globals this module declares further down: an array, a Vec and a struct
// element type. Exit code 6 + 30 + 7 = 43.
#include <stdlib::vec>
sumA -> long { t: long = 0; for x in LATER_A { t = t + x; } return t; }
sumV -> long { t: long = 0; for x in LATER_V { t = t + x; } return t; }
sumP -> long { t: long = 0; for p in LATER_P { t = t + p.x; } return t; }
main -> int { return (sumA() + sumV() + sumP()) as int; }
struct P { x: long }
LATER_A: [long; 3] = [1, 2, 3];
local LATER_V: Vec<long> = vec![10, 20];
LATER_P: Vec<P> = mkP();
mkP -> Vec<P> { v: Vec<P>; v.push(P { x: 3 }); v.push(P { x: 4 }); return v; }
