// A returned value converts only by lossless widening, as the language says of every conversion.
g x:long -> int { return x; }
main -> int { return g(5); }
