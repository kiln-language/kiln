#include <stdlib::atomic>

// An `asm` block's `out` into a local narrower than a word gives the local the register's low
// bytes as that type: sign-extended for a signed one, zero-extended for an unsigned one, whatever
// the upper bits held. The library's narrow atomics are such blocks (`lock xadd [rbx], {rax}`
// leaves the delta's upper bits above the old value).

local asI8 x:long -> i8 { r: i8 = 0; unsafe { asm { in rax x; out r rax; } } return r; }
local asU8 x:long -> u8 { r: u8 = 0; unsafe { asm { in rax x; out r rax; } } return r; }
local asI16 x:long -> i16 { r: i16 = 0; unsafe { asm { in rax x; out r rax; } } return r; }
local asU16 x:long -> u16 { r: u16 = 0; unsafe { asm { in rax x; out r rax; } } return r; }
local asI32 x:long -> int { r: int = 0; unsafe { asm { in rax x; out r rax; } } return r; }
local asU32 x:long -> u32 { r: u32 = 0; unsafe { asm { in rax x; out r rax; } } return r; }

main -> int {
    if (asI8(0x180) != -128 || asI8(0x7F) != 127) { return 1; }
    if (asU8(0x1FF) != 255) { return 2; }
    if (asI16(0x1234FFFB) != -5) { return 3; }
    if (asU16(0x1234FFFB) != 65531) { return 4; }
    if (asI32(0x180000000) != 0 - 2147483648) { return 5; }
    if (asU32(0x100000005) != 5) { return 6; }
    a: Atomic<i16> = Atomic.new(-5 as i16);
    if (a.add(3 as i16) != (-5 as i16) || a.load() != (-2 as i16)) { return 7; }
    if (a.swap(-300 as i16) != (-2 as i16) || a.load() != (-300 as i16)) { return 8; }
    if (a.cas(-300 as i16, 9 as i16) != (-300 as i16) || a.load() != (9 as i16)) { return 9; }
    b: Atomic<u8> = Atomic.new(200 as u8);
    if (b.add(100 as u8) != (200 as u8) || b.load() != (44 as u8)) { return 10; }
    c: Atomic<i8> = Atomic.new(-1 as i8);
    if (c.swap(5 as i8) != (-1 as i8)) { return 11; }
    return 0;
}
