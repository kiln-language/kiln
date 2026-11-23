// `x & 15` is in [0, 15]: not inside an 8-element array, so the check stays, and 12 panics.
var gX: long = 12;
pick x:long -> long { a: [long; 8]; for i in 0..8 { a[i] = i; } return a[x & 15]; }
main -> int { return pick(gX) as int; }
