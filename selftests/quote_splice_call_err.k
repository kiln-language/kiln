// `@(f())` where `f` gives a long: typed in place, it is no Node, and the refusal says how to
// splice it as a literal.
#include <stdlib::{ast, heap, vec}>
seven -> long { return 7; }
macro lit x:Node -> Node { return quote { @(seven()) + @x }; }
main -> int { return lit!(4) as int; }
