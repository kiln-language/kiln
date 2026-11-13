// A `HashMap` with a scalar key, built by the compiler and read at runtime. The key is hashed
// twice, once by the evaluator placing the entry and once by the emitted `probe` looking for it,
// and the two have to agree. They did not: a borrow of a scalar is the scalar, but `argValue`
// gave `hash &self` the address of its argument, so every entry landed in a slot the running
// program never probed. A `str` key was unaffected, which is why `gScalarNames` never showed it.
//
// One entry on its own is here because the first table that failed had three, and a collision was
// the obvious suspect. It is not: placement is wrong for a single key too.
//
// Exit code: 10 + 20 + 30 + 5 + 99 = 164.
#include <stdlib::map>

LONGKEYS: HashMap<long, long> = map![
    1 as long => 10 as long,
    2 as long => 20 as long,
    3 as long => 30 as long,
];
INTKEYS: HashMap<int, long> = map![ 7 => 5 as long ];
ONE: HashMap<long, long> = map![ 12345 as long => 99 as long ];

main -> int {
    n: long = 0;
    n = n + LONGKEYS.getOr(1 as long, 0);
    n = n + LONGKEYS.getOr(2 as long, 0);
    n = n + LONGKEYS.getOr(3 as long, 0);
    n = n + INTKEYS.getOr(7, 0);
    n = n + ONE.getOr(12345 as long, 0);
    return n as int;
}
