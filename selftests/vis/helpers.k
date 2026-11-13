// Three levels, one file. `local` is this file's own, `pkg` is the package's, `pub` is everyone's.
local secret -> long { return 1; }
pkg  shared  -> long { return 2; }
pub  open    -> long { return 3; }
// Reached from inside this file, which is what `local` allows.
pub useAll -> long { return secret() + shared() + open(); }
