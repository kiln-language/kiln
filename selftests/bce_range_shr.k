// An arithmetic shift keeps the sign: `x >> 60` of a long is in [-8, 7], and -1 panics.
var gX: long = -1;
pick x:long -> long { a: [long; 8]; return a[x >> 60]; }
main -> int { return pick(gX) as int; }
