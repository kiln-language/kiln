// `main` may return any integer type; the exit status is the low 8 bits.
main -> long {
    a: long = 300;
    return a + 2;          // 302: status 46
}
