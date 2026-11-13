// Inside the block `s` names the value the guard holds, reached through get()/set(). It has no
// address of its own, and the `&` used to take the address of a temporary and segfault.
#include <stdlib::io>
#include <stdlib::shared>
main -> int {
    s: Shared<long> = newShared(5 as long);
    with s { unsafe { println("addr = {}", &s); } }
    return 0;
}
