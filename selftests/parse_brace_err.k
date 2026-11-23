#include <stdlib::io>

// A `}` missing inside a function: the function's own `}` closes the loop instead, the declaration
// below it is read as part of the function, and the error is reported there, as it always was.
// The parse goes on from the next declaration, so the separate error further down is reported
// too, and nothing in between is.

count x:long -> long {
    n: long = x;
    while (n > 0) {
        n = n - 1;
    return n;
}

var gTotal: long = 0;

add x:long -> void { gTotal = gTotal + x; }

twice x:long -> long { return x * 2 }

main -> long { add(count(3)); return gTotal + twice(1); }
