// A global fn value holding a callee that takes its argument behind a lending type. A global's
// initializer is in no body the convention walk judged. Refused (batch 9); it released twice.
#include <stdlib::io>
struct Res { id: long }
methods Res for Drop { drop &self -> void { } }
struct Keep { r: Res }
stash r:Res -> long { k: Keep = Keep { r: r }; return k.r.id; }
gF: fn(Res)->long = &stash;
main -> int { r: Res = Res { id: 3 }; return gF(r) as int; }
