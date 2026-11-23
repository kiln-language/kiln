// `(a, b) = (b, a)` stores into a tuple the parentheses make, then throws it away: nothing is
// swapped. The destructure is written without them.
main -> int {
    lo: long = 1;
    hi: long = 2;
    (lo, hi) = (hi, lo);
    return lo as int;
}
