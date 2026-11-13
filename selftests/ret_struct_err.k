struct A { x: long }
struct B { x: long }
m -> A { b: B = B { x: 1 }; return b; }
main -> int { return m().x as int; }
