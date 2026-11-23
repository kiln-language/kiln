// What the store rule accepts: constants whose value fits (a literal, a char literal, literal
// arithmetic folded exactly), lossless widening, a literal operand taking a narrow operand's type
// (`c + 1` is a `u8`), compound assignment with such a literal, and `as`.
struct S { b: u8, w: u16 }
f n:long -> long { return n + 1; }
bump c:u8 -> u8 { return c + 1; }
main -> int {
    a: u8 = 200;
    b: u8 = 'a';
    d: u8 = 2 * 100;
    e: u8 = 300 - 100;
    k: char = -128;
    c: u8 = 250;
    c = c + 10;                     // a u8 sum, wrapped: 4
    c += 1;                         // 5
    n: long = f(299);
    w: u16 = n as u16;              // 300
    s: S = S { b: 255, w: 65535 };
    s.b += 2;                       // 1
    xs: [u8; 2] = [1, 'z'];
    xs[0] = xs[0] - 2;              // 255
    i: int = c;                     // widening
    l: long = i;
    x: u64 = 7;
    x = x * 3 + 1;                  // 22: the literals are u64s
    m: long = 1 << (l + 35);        // 1 << 40
    if (a != 200 || b != 97 || d != 200 || e != 200 || k != -128) { return 1; }
    if (c != 5 || w != 300 || s.b != 1 || xs[0] != 255 || l != 5 || x != 22) { return 2; }
    if (m != 1099511627776 || bump(255) != 0) { return 3; }
    return 0;
}
