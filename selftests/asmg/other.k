// Globals of another module, for `out_global` and `out_private_err`.
pub var gOther: long = 0;
pub var gOther8: i8 = 0;
local var gPriv: long = 0;

pub readOther -> long { return gOther; }
// Its own global, by its bare name, from its own block.
pub setOther x:long -> void { unsafe { asm { in rax x; out gOther rax; } } }
pub readPriv -> long { return gPriv; }
