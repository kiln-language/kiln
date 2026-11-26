// `n * 3 + 1` is one `lea` (`Scaler.foldArith`), here in an arm written as a conditional move;
// off with `--no-lea`, two.
// ir-has: lea_sum::steps lea [
// asm-has: lea_sum::steps *2 + 1]
steps n0:long -> long {
    n: long = n0;
    s: long = 0;
    while (n != 1) {
        if (n % 2 == 0) { n = n / 2; } else { n = n * 3 + 1; }
        s += 1;
    }
    return s;
}
main -> int {
    if (steps(27) != 111 || steps(97) != 118) { return 1; }
    return 0;
}
