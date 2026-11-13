// The trait LENDS `r`; this implementation consumes it. A caller reaching the method through the
// object reads the contract, keeps ownership, and releases what the impl already released.
#include <stdlib::io>
struct Res { id: long }
methods Res for Drop { drop &self -> void { println("release {}", self.id); } }
trait Sink2 { swallow &self r:Res -> long; }
struct Keeper { held: Res }
methods Keeper for Sink2 { swallow &self sink r:Res -> long { self.held = r; return self.held.id; } }
main -> int { return 0; }
