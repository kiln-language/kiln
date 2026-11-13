// Destructuring names one local per element.
mk -> (long, long) { return (1, 2); }
main -> int { a, b, c = mk(); return 0; }
