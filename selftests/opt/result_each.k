// A result built in a slot of its own at each return (`Option.Some(i)` at one, `Option.None` at
// another) is built in the caller's memory, `$sret`, at each (`Flow.buildInPlaceEach`): no frame
// slot, and no copy of its bytes at either `return`.
// ir-lacks: result_each::find aggcopy
// asm-lacks: result_each::find [rbp
#include <stdlib::option>
find xs:[long] k:long -> Option<long> {
    for i in 0..xs.len { if (xs[i] == k) { return Option.Some(i); } }
    return Option.None;
}
main -> int {
    a: [long; 8] = [1, 2, 3, 4, 5, 6, 7, 8];
    f: fn([long], long) -> Option<long> = &find;
    s: long = 0;
    for k in 0..10 {
        match f(a[..], k) { Some(i) { s += i; } None { s += 100; } }
    }
    if (s != 228) { return 1; }
    return 0;
}
