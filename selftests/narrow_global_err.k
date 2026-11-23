// A global's initializer (run by the evaluator) is held to the rule as well.
f n:long -> long { return n * 2; }
G: char = f(3);
main -> int { return G as int; }
