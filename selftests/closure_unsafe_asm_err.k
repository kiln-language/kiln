#include <stdlib::{io}>

// An `asm` block inside a closure written in safe code is refused.

viaObj f:Fn() -> void -> void { f(); }

main -> long {
    r: long = 0;
    viaObj(|| { asm { "mov rax, 7" out r rax; } });
    return r;
}
