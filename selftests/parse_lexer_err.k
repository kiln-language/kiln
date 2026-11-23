#include <stdlib::io>

// Errors the lexer finds are reported and gone on from like the parser's, since the lexer is
// always past the text an error is about. The `';` the skip after the first one reads as another
// bad character literal is not reported: nothing is, until the next declaration.

a -> long { x: char = 'ab'; return 1; }

b -> long { return 2 }

c -> long { y: long = 3 $ 4; return y; }

d -> long { return 0x; }

main -> long { return a() + b() + c() + d(); }
