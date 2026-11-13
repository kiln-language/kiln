// A for-in element handed to a read-only `&T` parameter of a recursive function (sqlmini's
// `for arg in args { vals.push(eval(arg, ctx)); }`). It was refused: "'arg' is handed to 'eval',
// which writes it". One `match` arm bound a borrow `v` of `e`'s payload; a sibling arm declared
// its own `v` and assigned it, and the guard, keying borrow locals by name over the whole body,
// took that assignment for a write through the first `v` into `e`.
// 3 + -4 + 10 + 7 = 16, and four leaves counted: 20.
#include <stdlib::{vec, heap, string}>
enum Expr { Num(long), Name(String), Neg(Box<Expr>), Call(Vec<Expr>) }
struct Ctx { n: long }
eval e:&Expr inout ctx:Ctx -> long {
    match e {
        Name(v) { ctx.n = ctx.n + 1; return v.length(); }
        Num(v) { ctx.n = ctx.n + 1; return v; }
        Neg(x) {
            v: long = 0;
            v = eval(x.at(), ctx);
            return 0 - v;
        }
        Call(args) {
            vals: Vec<long>;
            for arg in args { vals.push(eval(arg, ctx)); }
            t: long = 0;
            for v in vals { t = t + v; }
            return t;
        }
    }
}
main -> int {
    xs: Vec<Expr>;
    xs.push(Expr.Num(3));
    xs.push(Expr.Neg(newBox(Expr.Num(4))));
    xs.push(Expr.Num(10));
    xs.push(Expr.Name(stringOf("sevenAB")));
    e: Expr = Expr.Call(xs);
    c: Ctx = Ctx { n: 0 };
    r: long = eval(e, &c);
    return (r + c.n) as int;
}
