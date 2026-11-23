// Same width, other signedness: not every `int` is a `u32`.
f n:int -> int { return n - 1; }
main -> int {
    u: u32 = f(0);
    return (u % 7) as int;
}
