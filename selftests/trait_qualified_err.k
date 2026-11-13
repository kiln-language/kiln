// `Show.text(x)` on a type that does not implement Show.
pub trait Show { text &self -> long; }
struct P { v: long }
struct Q { v: long }
methods P for Show { text &self -> long { return self.v; } }
main -> int {
    q: Q = Q { v: 2 };
    return Show.text(q) as int;
}
