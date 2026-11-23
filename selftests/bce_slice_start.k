// A slice with no end written holds its start to the length, and reports it as a slice start
// ("panic: slice start 5 out of range for length 3"), not as an end. The two inclusive edges
// (a start equal to the length, and a start equal to the end) are in range and must pass.
from xs:[long] k:long -> long { return xs[k..].len; }
part xs:[long] i:long j:long -> long { return xs[i..j].len; }

main -> int {
    a: [long; 3];
    if (from(a[..], 3) != 0) { return 1; }
    if (part(a[..], 2, 2) != 0) { return 2; }
    if (part(a[..], 0, 3) != 3) { return 3; }
    return from(a[..], 5) as int;      // panics: exit 134
}
