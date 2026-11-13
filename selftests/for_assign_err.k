// `r` is a borrow of the element: its fields may be written, the borrow not re-aimed.
#include <stdlib::vec>
struct Res { id: long }
main -> int { rs: Vec<Res>; rs.push(Res { id: 1 }); for r in &rs { r = Res { id: 2 }; } return 0; }
