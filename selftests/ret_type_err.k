// A `return` is a store into the result: a str is no int.
f -> int { s: str = "a"; return s; }
main -> int { return f(); }
