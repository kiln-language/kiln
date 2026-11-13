// Three traits give P a `text`: the plain call names all three.
pub trait Show { text &self -> long; }
pub trait Debug2 { text &self -> long; }
pub trait Later { text &self -> long; }
struct P { v: long }
methods P for Show { text &self -> long { return self.v; } }
methods P for Debug2 { text &self -> long { return self.v * 100; } }
methods P for Later { text &self -> long { return 9; } }
main -> int {
    p: P = P { v: 2 };
    return (Later.text(p) + p.text()) as int;
}
