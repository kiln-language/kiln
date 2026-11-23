// A sum of two u8s is a u8 (it wraps at 256), so it lies in [0, 255]: that bounds it below a
// 256-element array's length, but not below a 255-element one's. 254 + 1 is 255: the check stays.
var gA: [long; 255];
var gX: long = 254;
var gY: long = 1;
pick x:u8 y:u8 -> long { return gA[(x + y) as long]; }
main -> int { return pick(gX as u8, gY as u8) as int; }
