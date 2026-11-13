// A generic function's own bound is held at the call: `int` has no `Default`.
trait Default { new -> Self; }
reset<T: Default> old:T -> T { return T.new(); }
main -> int { x: int = reset(5); return x; }
