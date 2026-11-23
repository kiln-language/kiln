// An immutable global is what the compiler computed for the whole run, and so is every block its
// value owns: a read of a constant offset in one is the number laid there, and what was read of
// one survives a store through any pointer, a call and a write to a `var` global, so it is read
// once and may leave a loop.
// ir-lacks: roglobals::fieldB ptrload
// ir-has: roglobals::fieldB const 5
// ir-lacks: roglobals::thirdNum ptrload
// ir-count: roglobals::acrossCall ptrload 2
// ir-before: roglobals::loopSum ptrload .L0
#include <stdlib::vec>
struct Table { a: long, b: long, c: long }
T: Table = Table { a: 3, b: 5, c: 7 };
NUMS: Vec<long> = vec![10, 20, 30];
var gX: long = 0;
var gSink: long = 0;

fieldB -> long { return T.b; }
thirdNum -> long { return NUMS[2]; }

// Big enough, and called from two places, to stay a call; it writes a global.
noise k:long -> void {
    s: long = 0;
    for i in 0..k { s = s + i * 3; s = s ^ (s >> 2); s = s + (i & 5); s = s - (s >> 3); }
    for i in 0..k { s = s + i * 7; s = s ^ (s >> 1); s = s + (i | 9); s = s - (s >> 4); }
    gSink = gSink + s;
}
acrossCall i:long -> long {
    x: long = NUMS[i];
    noise(i);
    return x + NUMS[i];
}
loopSum k:long -> long {
    s: long = 0;
    for i in 0..k { s = s + NUMS[i % 3]; gX = gX + 1; }
    return s;
}

main -> int {
    if (fieldB() != 5) { return 1; }
    if (thirdNum() != 30) { return 2; }
    if (acrossCall(1) != 40) { return 3; }
    noise(2);
    if (loopSum(4) != 70 || gX != 4) { return 4; }
    return 0;
}
