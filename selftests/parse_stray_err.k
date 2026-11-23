#include <stdlib::io>

// Tokens that cannot begin a declaration, at the top level: each is reported once, and the parse
// goes on with the next declaration. The `}` that closes nothing is skipped with the `42;`.

f -> long { return 1; }
)
g -> long { return 2; }
42;
}
h x:long -> long { return x + }

main -> long { return f() + g() + h(1); }
