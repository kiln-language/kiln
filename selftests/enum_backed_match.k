// A backed enum is matched by its value (it has no `$tag`), and its `Display` sees the value
// however it was reached: a local, a parameter, a constant `E.V` in a `...any` run, `format`,
// and the compile-time evaluator. `self as long`, `k: E = self` and `match self` agree.
#include <stdlib::io>
#include <stdlib::string>
#include <stdlib::fmt>

enum Err: long { Ip = 0, Port = 1, Missing = 7 }
methods Err for Display {
    display &self w:Write -> void {
        k: long = self as long;
        j: Err = self;
        m: str = "?";
        match self { Ip { m = "ip"; } Port { m = "port"; } _ { m = "other"; } }
        writeTo(w, "{}:{}:{}", m, k, j as long);
    }
}
methods Err {
    code &self -> long { match self { Ip { return 10; } Missing { return 70; } _ { return 0; } } }
    codeV self -> long { match self { Port { return 1; } _ { return 5; } } }
}
classify e:Err -> long { match e { Port { return 2; } _ { return 9; } } }
shown e:Err -> String { return format("{}", e); }

describe -> long {
    s: String = format("{} {} {}", Err.Ip, Err.Missing, shown(Err.Port));
    if (!s.eq("ip:0:0 other:7:7 port:1:1")) { return -1; }
    return Err.Missing.code() + classify(Err.Port) + Err.Port.codeV();
}
FOLDED: long = describe();

main -> int {
    a: Err = Err.Missing;
    if (FOLDED != 73) { return 1; }
    if (describe() != 73) { return 2; }
    if (!format("{}", a).eq("other:7:7")) { return 3; }
    if (!format("{}|{}", Err.Ip, a).eq("ip:0:0|other:7:7")) { return 4; }
    if (a.code() != 70 || a.codeV() != 5 || classify(a) != 9) { return 5; }
    match a { Missing { } _ { return 6; } }
    println("{} {}", Err.Port, a);
    return 0;
}
