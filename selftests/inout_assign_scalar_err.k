// A `&self` of a backed enum receives the value itself: assigning it would change only the
// method's copy, so the store is refused rather than silently lost.
enum Dir: long { Up = 0, Down = 1 }
methods Dir { flip &self -> void { self = Dir.Down; } }
main -> int { d: Dir = Dir.Up; d.flip(); return d as int; }
