// A method's own type parameter's bound, held at the call.
trait Show { show &self -> long; }
struct L { x: long }
methods L { pick<U: Show> &self u:U -> long { return u.show(); } }
main -> int { l: L = L { x: 1 }; return l.pick(5) as int; }
