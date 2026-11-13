// The other half of the same rule.
local twice x:long -> long { return x * 2; }
main -> int { return twice() as int; }
