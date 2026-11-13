// An owning element is borrowed, never moved out of the collection.
#include <stdlib::vec>
#include <stdlib::string>
struct Res { name: String }
keep sink r:Res -> long { return r.name.len; }
main -> int { rs: Vec<Res>; rs.push(Res { name: format("a") }); n: long = 0; for r in rs { n = n + keep(r); } return n as int; }
