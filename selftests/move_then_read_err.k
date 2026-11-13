// Operands are evaluated left to right, so a value moved by one argument is gone for the next:
// `f(take(r), look(r))` reads `r` after `take` was handed it.
#include <stdlib::string>
take s:String -> long { t: String = s; return t.len; }
look s:String -> long { return s.len; }
f a:long b:long -> long { return a + b; }
main -> int { r: String = stringOf("abc"); return f(take(r), look(r)) as int; }
