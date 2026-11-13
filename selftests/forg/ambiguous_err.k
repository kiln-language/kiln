// Two included modules declare `gDup`: the loop cannot tell which it walks, and says so.
#include <stdlib::vec>
#include <{tables, other}>

main -> int {
    s: long = 0;
    for x in gDup { s = s + x; }
    return s as int;
}
