// `f!(...)` on a plain function is an error.
square x:long -> long { return x * x; }
main -> int { return square!(3) as int; }
