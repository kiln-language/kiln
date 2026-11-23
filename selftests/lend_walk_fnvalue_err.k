// The same through a fn value: any addressed function may be the one called. Refused (batch 9).
#include <stdlib::{io, vec}>
var gV: Vec<long>;
grow -> void { gV.push(5); }
walk xs:&Vec<long> -> long { t: long = 0; for x in xs { grow(); t = t + x; } return t; }
main -> int { gV.push(1); f: fn(Vec<long>)->long = &walk; return f(gV) as int; }
