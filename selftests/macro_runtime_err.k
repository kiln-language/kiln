// A macro's value argument must be something the compiler can compute: a runtime local is not.
macro square x:long -> long { return x * x; }
main -> int { n: long = 4; return square!(n) as int; }
