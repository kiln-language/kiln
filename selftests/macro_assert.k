// `assert` as a real macro: the argument arrives as a TREE (its parameter is a Node), the body
// builds the code to splice with `quote`, `@cond` puts the caller's tree into it, and
// `sourceOf` turns the tree back into the text the message shows. The parser's builtin
// `assert!` steps aside when a macro of that name is in scope. The third assertion fails, and
// the panic's abort is exit code 134; the message must read exactly as the builtin's did.
#include <stdlib::ast>
#include <stdlib::heap>
#include <stdlib::vec>
#include <stdlib::io>

macro assert cond:Node -> Node {
    text: String = sourceOf(&cond);
    msg: String;
    msg.pushStr("assertion failed: ");
    msg.pushString(text);
    m: str = "";
    unsafe { m = msg.view(); }
    return quote { if (!@cond) { panic(@(Node.Str(m))); } };
}

main -> int {
    a: long = 5;
    b: long = 2;
    assert!(a > b);
    assert!(a * 2 == 10 && b < a);
    println("held");
    assert!(a * 2 > b + 10);
    println("not reached");
    return 0;
}
