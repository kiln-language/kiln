// `<pkg::{a, b}>` is one include per name, of that package; `<{a, b}>` the same for this
// package's own modules. Both lists below, and every module each names, reach the program.
// Exit code 11 + 3 = 14.
#include <stdlib::{vec, string,  io }>
#include <{one, two}>
main -> int {
    v: Vec<long>; v.push(1); v.push(2);
    s: String = format("{}", oneValue() + twoValue());
    return (s.len + oneValue() + twoValue() + v.len() - 2 + 1) as int;
}
