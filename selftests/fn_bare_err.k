// A fn value is `&name`. A bare function name where a value is wanted is refused, rather than
// typed as nothing and lowered as a load of a global that does not exist.
twice x:long -> long { return x * 2; }
main -> int { f: fn(long)->long = twice; return f(21) as int; }
