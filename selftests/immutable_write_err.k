// An assignment into a plain global is refused: a global is immutable unless declared `var`.
N: long = 7;
main -> int { N = 8; return 0; }
