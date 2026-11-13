// A `sink` parameter was given away to this frame and is released when it ends, so a borrow
// into one dangles exactly like a borrow of a local.
#include <stdlib::vec>
struct Res { id: long }
bad sink v:Vec<Res> -> &Res { return v.at(0); }
main -> int { return 0; }
