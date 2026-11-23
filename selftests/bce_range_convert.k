// A conversion that does not keep the range: a u16 in [0, 65535] read as an i16 may be negative
// (40000 is -25536), so indexing a 65536-element array with it keeps its check.
var gN: long = 40000;
var gA: [long; 65536];
pick n:long -> long {
    if (n < 0 || n > 65535) { return 0; }
    v: u16 = n as u16;
    return gA[(v as i16) as long];
}
main -> int { return pick(gN) as int; }
