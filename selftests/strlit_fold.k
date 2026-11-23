// The length of a string literal read through an inlined body is folded: escapes are one byte.
len s:str -> long { return s.len; }
first s:str -> long { return s[0] as long; }
main -> int {
    if (len("a\nb") != 3 || len("\t\\\"") != 3 || len("") != 0 || len("plain") != 5) { return 1; }
    if (first("\nx") != 10 || first("z") != 122) { return 2; }
    return 0;
}
