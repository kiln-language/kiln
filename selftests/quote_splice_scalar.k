// `@(n)` in a quote with `n` a scalar or a str: the literal holding its value (it used to splice
// the integer as if it were a Node, silently: garbage). A long, an int, a bool, a field, a str,
// a literal, and a Node beside them. 40 + 2 + 1 + 7 + 3 ("abc") + 5 + 4 = 62.
#include <stdlib::{ast, heap, vec, string}>
struct Cfg { width: long }
macro lit x:Node -> Node {
    n: long = 40;
    k: int = 2;
    yes: bool = true;
    c: Cfg = Cfg { width: 7 };
    s: str = "abc";
    return quote { @(n) + @(k) + (@(yes) as long) + @(c.width) + strLen(@(s)) + @(5) + @x };
}
strLen s:str -> long { return s.len; }
main -> int {
    return lit!(4) as int;
}
