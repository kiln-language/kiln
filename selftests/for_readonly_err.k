// In `for r in rs` a struct element is read where it lies, and read-only: `&rs` lends it.
#include <stdlib::vec>
struct Res { id: long }
methods Res { bump &self -> void { self.id = self.id + 1; } }
main -> int { rs: Vec<Res>; rs.push(Res { id: 1 }); for r in rs { r.bump(); } return 0; }
