// A product of two chars is a char: 100 * 3 wraps to 44, but 100 * 2 is -56, and a char's range
// reaches below zero, so indexing with one keeps its check (the low side) even into 128 elements.
var gA: [long; 128];
var gX: long = 100;
var gY: long = 2;
pick x:char y:char -> long { return gA[(x * y) as long]; }
main -> int { return pick(gX as char, gY as char) as int; }
