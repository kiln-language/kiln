// A constant is accepted when its value fits; 200 + 100 does not fit a `u8`.
main -> int {
    c: u8 = 200 + 100;
    return c as int;
}
