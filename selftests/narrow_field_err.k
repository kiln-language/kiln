// A struct literal's field is a store into the field.
struct S { b: u8, i: int }
f n:long -> long { return n + 1; }
main -> int {
    s: S = S { b: 1, i: f(1) };
    return s.i;
}
