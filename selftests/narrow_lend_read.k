#include <stdlib::{io}>

// A narrow signed local written through its address (an `inout` lend, a closure's capture) at
// its own width, then read by name and widened: the read extends it again, so a value that
// changed sign reads as itself and not as the old upper bytes over the new lower ones. Locals,
// a parameter, and `var` globals.

viaObj f:Fn() -> void -> void { f(); }
setInt inout x:int v:int -> void { x = v; }
setShort inout x:i16 v:i16 -> void { x = v; }
setByte inout x:i8 v:i8 -> void { x = v; }

viaInout -> long { x: int = -1; setInt(&x, 5); return x as long; }
viaClosure -> long { x: int = -1; viaObj(|| { x = 5; }); return x as long; }
backNegative -> long { x: int = 7; setInt(&x, -3); return x as long; }
shortOne -> long { x: i16 = -1; setShort(&x, 300); return x as long; }
byteOne -> long { x: i8 = 100; setByte(&x, -100); return x as long; }
param x:int -> long { setInt(&x, 9); return x as long; }
compared -> bool { x: int = -1; setInt(&x, 5); return x == 5; }
var gX: int = -1;
var gS: i16 = 7;
globals -> long { setInt(&gX, 5); setShort(&gS, -2); return (gX as long) * 100 + (gS as long); }

main -> int {
    if (viaInout() != 5) { return 1; }
    if (viaClosure() != 5) { return 2; }
    if (backNegative() != -3) { return 3; }
    if (shortOne() != 300) { return 4; }
    if (byteOne() != -100) { return 5; }
    if (param(-2) != 9) { return 6; }
    if (!compared()) { return 7; }
    if (globals() != 498) { return 8; }
    println("narrow_lend_read");
    return 0;
}
