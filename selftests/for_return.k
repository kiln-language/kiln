// A `return` inside `for x in v`, where the function owns `v`, releases `v` on the way out. That
// release is not the loop body writing `v`: the loop is abandoned before it runs. Search-and-return
// over a value the function owns, or one bound out of a match arm, is the common shape.
#include <stdlib::io>
#include <stdlib::string>
#include <stdlib::vec>
#include <stdlib::result>

firstEmpty s:str -> long {
    parts: Vec<str> = strSplit(s, '.');
    i: long = 0;
    for p in parts { if (p.len == 0) { return i; } i = i + 1; }
    return -1;
}
twoLetter xs:Result<Vec<String>, long> -> long {
    match xs {
        Ok(v) { k: long = 0; for a in v { if (a.length() == 2) { return k; } k = k + 1; } }
        Err(e) { return e; }
    }
    return -1;
}
// The loop still may not change what it walks: only the exit releases are exempt.
main -> int {
    if (firstEmpty("a.b.c") != -1 || firstEmpty("a..c") != 1) { return 1; }
    v: Vec<String>;
    v.push(stringOf("abc")); v.push(stringOf("de")); v.push(stringOf("f"));
    if (twoLetter(Result.Ok(v)) != 1) { return 2; }
    if (twoLetter(Result.Err(7)) != 7) { return 3; }
    return 0;
}
