// A narrow operation wraps at its width, so its result lies in its type's range: `x + y` of two
// u8s indexes 256 elements with no check, and reads the wrapped element (200 + 100 is 44); `a * b`
// of two u16s indexes 65536. An i16's `x - y` may be negative: its check stays.
// ir-lacks: narrow_range::sum8 bounds
// ir-lacks: narrow_range::mul16 bounds
// ir-has: narrow_range::sub16 bounds
var gX: long = 200;
var gY: long = 100;
var gT: [long; 256];
var gW: [long; 65536];
sum8 x:u8 y:u8 -> long { return gT[(x + y) as long]; }
mul16 a:u16 b:u16 -> long { return gW[(a * b) as long]; }
sub16 a:i16 b:i16 -> long { return gW[(a - b) as long]; }
main -> int {
    for i in 0..256 { gT[i] = i; }
    if (sum8(gX as u8, gY as u8) != 44) { return 1; }
    gW[(gX * 400) & 65535] = 7;
    if (mul16(gX as u16, 400 as u16) != 7) { return 2; }
    if (sub16(gX as i16, gY as i16) != 0) { return 3; }
    return 0;
}
