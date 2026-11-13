// Lending a field of a method's result to an `inout` parameter: the argument is typed once (the
// array-lend check read it before it was typed, and typing it twice looked `at` up under its
// already-resolved name). Exit code: the swapped vector's length, 1, plus `n`, 1.
#include <stdlib::{io, vec, mem}>
struct G { xs: Vec<long>, n: long }
main -> int {
    gs: Vec<G>;
    a: Vec<long>; gs.push(G { xs: a, n: 1 });
    mine: Vec<long>; mine.push(5);
    swapValues(&mine, &gs.at(0).xs);
    return (gs.at(0).xs.len() + gs.at(0).n) as int;
}
