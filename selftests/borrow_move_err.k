// `+` through a borrow is the borrowed type's `Add`, whose `self` is taken by value: a String
// cannot be moved out of a borrow for it.
#include <stdlib::string>
grow w:&String -> String { return w + "x"; }
main -> int { s: String = stringOf("a"); t: String = grow(&s); return t.len as int; }
