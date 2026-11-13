// Only `pub` crosses an object boundary. `local` and `pkg` are internal to this object, so a
// name nothing here defines is a name nothing can ever call.
local hidden x:long -> long;
main -> int { return 0; }
