// `-> never`: a function that does not come back. A call to one ends its path for the return
// check, definite initialization and ownership; its body is held to never reaching its end.
struct Res { n: long }
var gDropped: long = 0;
methods Res for Drop { drop &self -> void { gDropped = gDropped + 1; } }

die code:long -> never {
    unsafe { asm -> never { in rdi code; "mov rax, 60" "syscall" } }
}
// A never function may end in another one, or loop for ever.
fail2 code:long -> never { die(code + 1); }
spin -> never { loop { } }

pick x:long -> long {
    if (x > 0) { return x; }
    die(3);                      // no `return` needed after it
}
// Definitely assigned after the if: the else path does not come back.
settle c:bool -> long {
    v: long;
    if (c) { v = 5; } else { fail2(4); }
    return v;
}
// An owning local moved on one path and not on the other: the never path releases nothing.
keep c:bool -> long {
    r: Res = Res { n: 7 };
    if (c) { consume(r); } else { die(9); }
    return gDropped;
}
consume r:Res -> void { }
methods Res {
    stop &self code:long -> never { die(code); }
}
main -> long {
    if (pick(1) != 1) { return 1; }
    if (settle(true) != 5) { return 2; }
    if (keep(true) != 1) { return 3; }
    r: Res = Res { n: 1 };
    if (r.n == 0) { r.stop(5); }
    return 42;
}
