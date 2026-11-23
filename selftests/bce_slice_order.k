// A slice whose start is past its end ("panic: slice start 2 is past slice end 1") has its own
// report, separate from an end past the length.
part xs:[long] i:long j:long -> long { return xs[i..j].len; }

main -> int {
    a: [long; 3];
    if (part(a[..], 1, 1) != 0) { return 1; }
    return part(a[..], 2, 1) as int;   // panics: exit 134
}
