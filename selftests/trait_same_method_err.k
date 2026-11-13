// `p.text()` where two `pub` traits each give P a `text`: refused, naming both and the way out.
pub trait Show { text &self -> long; }
pub trait Debug2 { text &self -> long; }
struct P { v: long }
methods P for Show { text &self -> long { return self.v; } }
methods P for Debug2 { text &self -> long { return self.v * 100; } }
main -> int {
    p: P = P { v: 2 };
    return p.text() as int;
}
