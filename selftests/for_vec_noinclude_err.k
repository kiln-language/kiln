// `for x in v` over a `Vec` in a file that does not include `stdlib::vec` (here a program with a
// macro, which pulls `stdlib::ast`, and with it `vec`, in only after this file is read). It said
// "cannot walk a Vec<long> with `for x in`"; the type is what is unknown, and the include says so.
macro twice x:Node -> Node { return quote { @x + @x }; }
main -> int {
    v: Vec<long>;
    t: long = 0;
    for x in v { t = t + x; }
    return (t + twice!(1)) as int;
}
