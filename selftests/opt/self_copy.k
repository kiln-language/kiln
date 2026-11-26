// A small function calling itself has that call replaced by copies of its body, two levels
// deep (`Relayout.selfInline`), so one call is left where three levels of the recursion were,
// and each copy adds straight into the accumulator (`srMergeAt`): no second accumulator is
// set to zero for a copy.
// asm-count: self_copy::fib call 1
// asm-count: self_copy::fib mov r13d, 0 1
fib n:long -> long {
    if (n < 2) { return n; }
    return fib(n - 1) + fib(n - 2);
}
main -> int {
    if (fib(20) != 6765) { return 1; }
    return 0;
}
