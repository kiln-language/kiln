// An `asm` block's `out` into a global writes the global: read back directly, through a call and
// through a fn value, and by a later block's `in`. This module's globals are named bare, as
// another module's are (`other.k`); a local spelled like a global is the one written where it is
// in scope. A narrow global gets the register's low bytes as its type, whatever was above them.
#include <other>

var gWide: long = 0;
var gI16: i16 = 0;
var gU8: u8 = 0;
var gF: f64 = 0.0;
var gCount: long = 0;

local readWide -> long { return gWide; }

local setWide x:long -> void { unsafe { asm { in rax x; out gWide rax; } } }
local setI16 x:long -> void { unsafe { asm { in rax x; out gI16 rax; } } }
local setU8 x:long -> void { unsafe { asm { in rcx x; out gU8 rcx; } } }
local setF bits:long -> void { unsafe { asm { in rax bits; "movq xmm1, rax" out gF xmm1; } } }
// Read with `in` and written with `out` in one block.
local bump -> void { unsafe { asm { in rax gCount; "add rax, 1" out gCount rax; } } }
// A local of a global's spelling: the block writes the local, and the global is left alone.
local shadow x:long -> long {
    gWide: long = 0;
    unsafe { asm { in rax x; out gWide rax; } }
    return gWide;
}

main -> int {
    setWide(0x123456789);
    if (gWide != 0x123456789) { return 1; }
    if (readWide() != 0x123456789) { return 2; }
    f: fn() -> long = &readWide;
    setWide(77);
    if (f() != 77) { return 3; }
    setI16(0x1234FFFB);
    if (gI16 != -5) { return 4; }
    setU8(0x1FF);
    if (gU8 != 255) { return 5; }
    setF(0x4004000000000000);
    if (gF != 2.5) { return 6; }
    for i in 0..10 { bump(); }
    if (gCount != 10) { return 7; }
    if (shadow(42) != 42 || gWide != 77) { return 8; }
    setOther(-9);
    if (gOther != -9 || readOther() != -9) { return 9; }
    unsafe { asm { in rax 0x7FFF0081; out gOther8 rax; } }
    if (gOther8 != (-127 as i8)) { return 10; }
    return 0;
}
