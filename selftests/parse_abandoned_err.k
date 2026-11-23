#include <stdlib::io>

// A declaration taken back for an error leaves no type behind, and nothing that names the type is
// reported for it again: every use of `Shape` and `Area` below would otherwise be an error of its
// own. An error in a declaration that names neither is still reported.

struct Shape { w: long, h }

trait Area { area &self -> long; scale &self k: -> long; }

methods Shape for Area { area &self -> long { return self.w * self.h; } }

struct Square { side: long }

methods Square for Area { area &self -> long { return self.side * self.side; } }

big s:Shape -> Shape { return Shape { w: s.w * 2, h: s.h * 2 }; }

g -> long { return 1 }

main -> long { q: Square = Square { side: 3 }; return q.side + g(); }
