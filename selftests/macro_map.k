// `map![k => v, ...]`: the pairs read back as code, the keys as a `Vec`, the values as the
// variadic of `mapOf`, so the destination types the values and a bare literal is not stuck as
// an `int`. `map![]` is empty. Exit code 47.
#include <stdlib::io>
#include <stdlib::map>
#include <stdlib::vec>

struct Table { byName: HashMap<str, long>, spare: HashMap<long, str> }

// A global one is computed by the compiler and placed in the binary, table and all.
RANK: HashMap<str, long> = map!["gold" => 1, "silver" => 2, "bronze" => 3];

main -> int {
    m: HashMap<str, long> = map!["a" => 1, "bb" => 22, "c, d" => 3 * 8];
    e: HashMap<str, long> = map![];
    t: Table = Table { byName: map!["x" => 40], spare: map![] };
    q: HashMap<long, str> = map![long, str: 1 => "one", 2 => "two"];
    println("{} {} {} {} {} {}", m.get("a") + m.get("bb") + m.get("c, d"), e.len(), t.byName.get("x"), t.spare.len(), q.get(2), m.has("zz"));
    return (m.get("bb") + m.get("c, d") + RANK.get("silver") - 1) as int;
}
