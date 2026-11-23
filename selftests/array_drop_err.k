// A global array of a Drop type built from another array: a global's initializer is in no
// function the ownership pass walks, so nothing could record the move. Refused (batch 8 refused
// every whole array of a Drop type; batch 9 moves one between locals and into fields).
#include <stdlib::string>
var gA: [String; 2];
var gB: [String; 2] = gA;
main -> int { return 0; }
