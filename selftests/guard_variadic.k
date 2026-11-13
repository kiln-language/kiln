// A parameter handed to a variadic run past the run's first argument is read, not written:
// every argument of the run is the one `...any` parameter. The guard took an argument past the
// declared parameters for an unknown one, so `say` was taken to write `what`, and handing it
// an immutable global was refused.
#include <stdlib::io>
NAME: str = "kiln";
say what:str -> void { println("{} {} {}", 1, 2, what); }
main -> int {
    say(NAME);
    if (NAME.len != 4) { return 1; }
    return 0;
}
