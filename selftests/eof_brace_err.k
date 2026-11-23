// A missing `}` is reported where the text ends, on the last line that has any, as gcc and
// clang report it, rather than at column 0 of the empty line after the final newline.
main -> int {
    return 0;
