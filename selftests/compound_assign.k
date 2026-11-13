// `x op= y` is `x = x op y` with the place evaluated once: on integers (every operator), floats,
// fields, array and Vec elements, through `*p`, and on a type whose operator is a trait (`Add`).
#include <stdlib::{core, vec, string}>
var calls: long = 0;
next -> long { calls = calls + 1; return calls - 1; }
struct P { x: long, y: long }
struct V2 { a: long }
methods V2 for Add<V2> { add self o:V2 -> V2 { return V2 { a: self.a + o.a }; } }
main -> int {
    n: long = 10;
    n += 5; n -= 3; n *= 4; n /= 6; n %= 5;      // 15, 12, 48, 8, 3
    b: long = 12;
    b &= 10; b |= 1; b ^= 3; b <<= 4; b >>= 2;   // 8, 9, 10, 160, 40
    u: u8 = 250;
    u += 3;                                      // 253
    f: f64 = 1.5;
    f *= 4.0; f -= 0.5;                          // 5.5
    p: P = P { x: 1, y: 2 };
    p.y += 40;                                   // 42
    arr: [long; 4] = [0, 0, 0, 0];
    arr[next()] += 7;                            // arr[0] = 7, next() once
    arr[next()] += 9;                            // arr[1] = 9
    v: Vec<long> = vec![1, 2, 3];
    v[next()] += 100;                            // v[2] = 103 (next() is 2)
    s: String = stringOf("ab");
    s += "cd";                                   // through String's Add<str>
    w: V2 = V2 { a: 2 };
    w += V2 { a: 3 };                            // 5
    q: long = 6;
    unsafe { pq: *long = &q as *long; *pq += 1; }   // 7
    if (calls != 3) { return 1; }
    if ((f * 2.0) as long != 11) { return 2; }
    return (n + b + (u as long - 250) + p.y + arr[0] + arr[1] + v[2] + s.len + w.a + q - 200) as int;
    // 3 + 40 + 3 + 42 + 7 + 9 + 103 + 4 + 5 + 7 = 223 - 200 = 23
}
