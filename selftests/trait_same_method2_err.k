// A generic body bound by both traits cannot tell either: refused at the stamped call.
pub trait Show { text &self -> long; }
pub trait Debug2 { text &self -> long; }
struct P { v: long }
methods P for Show { text &self -> long { return self.v; } }
methods P for Debug2 { text &self -> long { return self.v * 100; } }
both<T: Show + Debug2> x:T -> long { return x.text(); }
main -> int {
    p: P = P { v: 2 };
    return both(p) as int;
}
