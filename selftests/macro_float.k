// A float literal handed to a macro through `parseExpr` arrives as stdlib::ast's `Node.Float`, its
// spelling, and comes back as the same literal (it used to arrive as `Int(0)`: `vec![1.0, 2.0]`
// built zeros). Both in a body and in a global the evaluator folds.
#include <stdlib::vec>
G: Vec<f64> = vec![0.5, 4.25, -3.0];
main -> long {
    v: Vec<f64> = vec![1.0, 2.5];
    if (v.len() != 2 || v.get(0) != 1.0 || v.get(1) != 2.5) { return 1; }
    if (G.len() != 3 || G.get(0) != 0.5 || G.get(1) != 4.25 || G.get(2) != -3.0) { return 2; }
    return 42;
}
