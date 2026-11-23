// A scalar has no fields; this used to stop in lowering with an internal error.
main -> int { x: long = 5; return x.foo as int; }
