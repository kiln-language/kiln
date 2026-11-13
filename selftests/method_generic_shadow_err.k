// A method's own type parameter cannot reuse its block's.
struct W<T> { v: T }
methods W<T> { put<T> &self x:T -> void { } }
main -> int { return 0; }
