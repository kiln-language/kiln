// Same width, other signedness: explicit too.
h x:long -> u64 { return x; }
main -> int { return h(5) as int; }
