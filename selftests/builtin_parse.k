// `builtin parseExpr`: the compiler's parser, declared where a macro can call it, under a name of
// the declaring module's own (`builtin_parse::parseExpr`, not `ast::parseExpr`, so nothing here is
// the name the evaluator used to recognise). A raw macro reads its text back as code with it.
#include <stdlib::ast>
pub builtin parseExpr src:str -> Node;
macro twice src:str -> Node {
    e: Node = parseExpr(src);
    return quote { (@e) * 2 };
}
k: long = 4;
main -> long {
    n: long = 17;
    return twice![n + k];       // (17 + 4) * 2 = 42
}
