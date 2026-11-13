// Exit code: 40 + 2 from `+` in a module that does not include core, then 100 more from a drop.
#include <ops>
main -> int {
    s: long = sumV(V { x: 40 }, V { x: 2 });
    { r: Res = Res { n: 100 }; }
    return (s + gDropped - 100) as int;
}
