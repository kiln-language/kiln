// A trait's static method needs a destination to say which type's it is.
pub trait Fresh { new -> Self; }
struct P { a: long }
methods P for Fresh { new -> P { return P { a: 5 }; } }
methods P for Default { new -> P { return P { a: 7 }; } }
main -> long { Fresh.new(); return 0; }
