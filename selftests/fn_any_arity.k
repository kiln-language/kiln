// `FnN` is not declared anywhere: the compiler makes the trait for an arity when it first meets
// one (`Parser::fnTraitFor`). `stdlib::core` used to write out `Fn0`..`Fn4`, and `parseFnSugar`
// carried its own copy of that number, so five arguments was the ceiling and adding a sixth meant
// editing both. Seven works here without either file knowing the number seven.
//
// Exit code: 28 + 0 + 9 = 37.
#include <stdlib::io>

// Seven arguments, well past the old limit of four.
call7 g:Fn(long, long, long, long, long, long, long) -> long -> long {
    return g(1, 2, 3, 4, 5, 6, 7);
}

// Nothing at all, which is the other end of the same machinery.
call0 g:Fn() -> long -> long { return g(); }

// Through a trait object rather than a bound, so the vtable path is exercised too.
callBoxed g:Fn(long, long) -> long -> long { return g(3, 6); }

main -> int {
    seven: long = call7(|a: long, b: long, c: long, d: long, e: long, f: long, h: long| -> long {
        return a + b + c + d + e + f + h;
    });
    none: long = call0(|| -> long { return 0; });
    two: long = callBoxed(|x: long, y: long| -> long { return x + y; });

    println("seven={} none={} two={}", seven, none, two);
    return (seven + none + two) as int;
}
