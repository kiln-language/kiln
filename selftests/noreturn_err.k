// A non-void function that can reach its end without returning.
local pick n:long -> long { if (n > 0) { return 1; } }
main -> int { return pick(3) as int; }
