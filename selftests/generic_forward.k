// A generic type used above its declaration in the same file.
first p:Pair<long> -> long { return p.a; }
struct Pair<T> { a: T, b: T }
main -> int { p: Pair<long> = Pair<long> { a: 4, b: 5 }; return (first(p) + p.b) as int; }
