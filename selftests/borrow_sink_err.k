// A borrowed receiver handed to a parameter that takes it: the callee would release what the
// caller still owns. Refused, where it used to be accepted and released twice.
#include <stdlib::io>
struct Res { n: long }
methods Res for Drop { drop &self -> void { } }
struct W { r: Res }
take sink w:W -> long { return w.r.n; }
methods W { m &self -> long { return take(self); } }
main -> int { w: W = W { r: Res { n: 3 } }; return w.m() as int; }
