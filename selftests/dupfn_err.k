// Two functions of one name. The second used to replace the first in the checker's table while
// BOTH were emitted, and NASM reported a redefined label from a line of generated assembly.
local twice x:long -> long { return x * 2; }
local twice x:long -> long { return x * 3; }
main -> int { return twice(2) as int; }
