// An `asm` block's `out` is held to a global's visibility, as an assignment is.
#include <other>
main -> int {
    unsafe { asm { in rax 1; out gPriv rax; } }
    return readPriv() as int;
}
