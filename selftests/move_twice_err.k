// The same value handed on twice within one statement.
#include <stdlib::string>
take s:String -> long { t: String = s; return t.len; }
main -> int { r: String = stringOf("abc"); n: long = take(r) + take(r); return n as int; }
