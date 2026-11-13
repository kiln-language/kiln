// A method's own type parameter that nothing in the call says is refused, as a generic
// function's is.
struct L { n: long }
methods L { pick<X> -> long { return 0; } }
main -> int { L.pick(); return 0; }
