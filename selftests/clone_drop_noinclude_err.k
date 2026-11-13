// No derived clone for a type with a drop of its own, in a program that includes nothing.
struct R { x: long }
methods R for Drop { drop &self -> void { } }
main -> int { r: R = R { x: 1 }; s: R = r.clone(); return 0; }
