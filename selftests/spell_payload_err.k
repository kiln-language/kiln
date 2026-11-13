// A guard message names a place as the source does: the binding a `match` gave a payload, not the
// payload slot it borrows (`e.$Call$0`).
#include <stdlib::vec>
enum E { Call(Vec<long>), Lit(long) }
f e:&E -> long {
    match e { Call(args) { for a in args { args.push(a); } } _ { } }
    return 0;
}
main -> long { e: E = E.Call(vec![1]); return f(&e); }
