// The same for a slice and for an array of known length, by a constant or by a counted loop.
// ir-lacks: bce_slice::sums bounds
// ir-lacks: bce_slice::arr bounds
#include <stdlib::vec>
sums xs:[long] -> long { s: long = 0; for i in 0..xs.len { s = s + xs[i]; } return s; }
arr -> long {
    a: [long; 8];
    for i in 0..8 { a[i] = i * 3; }
    s: long = 0;
    for i in 0..8 { s = s + a[i]; }
    return s + a[3];
}
main -> int {
    b: [long; 5] = [1, 2, 3, 4, 5];
    if (sums(b[..]) != 15 || sums(b[1..3]) != 5 || arr() != 93) { return 1; }
    return 0;
}
