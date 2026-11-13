// A `str` is an immutable view of its bytes: `s[i]` reads one, and storing one is refused.
main -> int {
    s: str = "abc";
    s[1] = 65;
    return s[1] as int;
}
