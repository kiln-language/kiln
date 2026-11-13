// A call is held to the callee's arity. Too few arguments used to read whatever the argument
// register happened to hold; too many left the extras evaluated and dropped.
local twice x:long -> long { return x * 2; }
main -> int { return twice(1, 2) as int; }
