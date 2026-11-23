// A store a macro builds is held to what a written one is: here its target is the caller's
// argument, which the second time is a call.
#include <stdlib::ast>
next -> long { return 1; }
macro setThree t:Node -> Node { return quote { @t = 3; }; }
main -> int {
    x: long = 0;
    setThree!(x);
    setThree!(next());
    return x as int;
}
