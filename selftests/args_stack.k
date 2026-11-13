// More arguments than registers: past ten general and eight float ones, each goes on the stack in
// order (System V's rule for what the registers do not hold). Integers, floats past the eighth, an
// f32, a struct by value; a call with values live across it in every register; a fn value; the
// evaluator (`K16`). 2030215015 % 97 = 68, then 715, 715, 230 and 1930: 3658,
// returned as 3658 % 256 = 74.
#include <stdlib::string>
struct P { x: long, y: long, s: String }
mix a:long b:f64 c:long d:f64 e:long f:f64 g:long h:f64 i:long j:f64 k:long l:f64 m:long n:f64 o:long p:f64 q:long r:f64 s:long t:f32 u:P v:long w:f64 -> long {
    fs: f64 = b + d + f + h + j + l + n + p + r + w;
    return a + c + e + g + i + k + m + o + q + s + v + (fs as long) * 1000 + (t as long) * 100000 + u.x * 10000000 + u.y + u.s.length() * 1000000000;
}
many a:long b:long c:long d:long e:long f:long g:long h:long i:long j:long k:long l:long m:long n:long o:long p:long -> long {
    return a + b + c + d + e + f + g + h + i + j + k + l + m + n + o + p * 100;
}
K16: long = many(1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 7);
viaFn f:fn(long, long, long, long, long, long, long, long, long, long, long, long, long, long, long, long) -> long -> long {
    return f(2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2);
}
twelve a:long b:long c:long d:long e:long f:long g:long h:long i:long j:long k:long l:long -> long {
    return a + 2*b + 3*c + 4*d + 5*e + 6*f + 7*g + 8*h + 9*i + 10*j + 11*k + 12*l;
}
work n:long -> long {
    t: long = 0;
    for i in 0..n {
        x: long = i * 3; y: long = i * 5; z: long = i * 7; w: long = i + 11; q: long = i * i;
        t = t + twelve(i, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1) + x + y + z + w + q;
    }
    return t;
}
main -> int {
    p: P = P { x: 3, y: 4, s: stringOf("ab") };
    r: long = mix(1, 1.5, 1, 1.5, 1, 1.5, 1, 1.5, 1, 1.5, 1, 1.5, 1, 1.5, 1, 1.5, 1, 1.5, 1, 2.0 as f32, p, 1, 1.5);
    t: long = r % 97 + many(1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 7) + K16 + viaFn(&many) + work(10);
    return (t % 256) as int;
}
