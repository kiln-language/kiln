// A scalar `var` global lent to an `inout` parameter, while the callee writes the global by name.
#include <stdlib::{io}>
var gN: long = 0;
addTwice inout x:long -> void { x = x + 1; gN = gN + 10; x = x + 1; }
main -> long { addTwice(&gN); return gN; }
