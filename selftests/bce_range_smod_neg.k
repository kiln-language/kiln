// A signed `x % 8` of a value that may be negative is in [-7, 7]: the check stays, and -3 panics.
var gX: long = -3;
pick x:long -> long { a: [long; 8]; for i in 0..8 { a[i] = i; } return a[x % 8]; }
main -> int { return pick(gX) as int; }
