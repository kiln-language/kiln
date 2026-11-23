#include <stdlib::io>

// An unterminated string runs to the end of the file. The error before it is reported, then the
// string's, and nothing after it: the declarations inside the string's text are never read.

one -> long { return 1 }

name -> str { return "kiln; }

two -> long { return 2 }

main -> long { return one() + two(); }
