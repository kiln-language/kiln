// A generic callee is inferred from its arguments, so it cannot also be what infers them: here
// nothing says what `fixedOf`'s N is.
#include <stdlib::fixedstring>
lengthOf<T> x:T -> long { return 0; }
main -> int { return lengthOf(fixedOf("k")) as int; }
