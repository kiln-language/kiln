// `Vec<T>`'s clone is declared for `T: Clone`, and an element that owns a resource and has no
// clone does not meet it.
#include <stdlib::vec>
struct Res { fd: long }
methods Res for Drop { drop &self -> void { } }
main -> int { v: Vec<Res>; v.push(Res { fd: 1 }); w: Vec<Res> = v.clone(); return w.len() as int; }
