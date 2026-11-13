// Floats in the standard library: printing, parsing, the math methods, the total order, and
// Encode/Decode. Exits 0 when every check holds, otherwise the number of the first that did not.
// (build/try/f/ffuzz.py checks printing, parsing and the rounding methods against Python.)
#include <stdlib::{io, core, float, string, vec, sort, encode, option, result}>

struct Sample { x: f64, y: f32, n: long }

is s:String want:str -> bool { unsafe { return strEq(s.view(), want); } }
shown<T: Display> v:T -> String { s: String; v.display(s); return s; }

main -> int {
    // printing
    z: f64 = 0.0;
    if (!is(format("{} {} {} {}", 0.1, 1.0, -z, 1e100), "0.1 1.0 -0.0 1e100")) { return 1; }
    if (!is(format("{:.2} {:e} {:+.1} {:08.3}", 3.14159, 1500.0, 2.25, -2.5), "3.14 1.5e3 +2.2 -002.500")) { return 2; }
    third: f32 = 0.1;
    if (!is(format("{} {:.3e}", third, third), "0.1 1.000e-1")) { return 3; }
    if (!is(format("{} {} {:>5}|{:05}", INFINITY, -INFINITY, NAN, INFINITY), "inf -inf   NaN|  inf")) { return 4; }
    if (!is(shown(2.5), "2.5") || !is(shown(third), "0.1")) { return 5; }
    if (!is(format("{:x}", 1.0), "3ff0000000000000")) { return 6; }

    // parsing
    if (f64.parse("1e-3").unwrap() != 0.001 || f64.parse("-.5").unwrap() != -0.5) { return 10; }
    if (f64.parse("x").isSome() || f64.parse("1e").isSome() || f64.parse("").isSome() || f64.parse(" 1").isSome()) { return 11; }
    if (!f64.parse("-Infinity").unwrap().isInfinite() || !f64.parse("nan").unwrap().isNan()) { return 12; }
    if (f32.parse("16777217").unwrap() != 16777216.0) { return 13; }      // a tie, to even
    if (f64.parse("2.4703282292062328e-324").unwrap().toBits() != 1) { return 14; }   // just past half the least subnormal

    // rounding
    a: f64 = 2.5;
    b: f64 = -2.5;
    h: f64 = -0.5;
    if (a.round() != 3.0 || b.round() != -3.0 || a.floor() != 2.0 || b.ceil() != -2.0 || b.trunc() != -2.0) { return 20; }
    if (!h.ceil().isSignNegative() || !h.round().isSignNegative() || h.floor() != -1.0 || b.fract() != -0.5) { return 21; }
    big: f64 = 1e300;
    if (big.floor() != big || !INFINITY.floor().isInfinite() || !NAN.round().isNan()) { return 22; }

    // min, max, clamp, sign
    one: f64 = 1.0;
    if (NAN.min(one) != 1.0 || one.max(NAN) != 1.0 || !NAN.min(NAN).isNan()) { return 30; }
    if (z.max(-z).isSignNegative() || !z.min(-z).isSignNegative()) { return 31; }
    if (a.clamp(0.0, 1.0) != 1.0 || b.clamp(0.0, 1.0) != 0.0 || !NAN.clamp(0.0, 1.0).isNan()) { return 32; }
    if (b.abs() != 2.5 || a.copySign(-1.0) != -2.5 || NAN.isSignNegative() || !(-z).isSignNegative()) { return 33; }
    if (INFINITY.isFinite() || !one.isFinite() || NAN.isFinite() || NAN.isInfinite()) { return 34; }

    // sqrt, powi
    four: f64 = 4.0;
    two: f64 = 2.0;
    if (four.sqrt() != 2.0 || !b.sqrt().isNan() || two.powi(10) != 1024.0 || two.powi(-2) != 0.25 || two.powi(0) != 1.0) { return 40; }
    nine: f32 = 9.0;
    if (nine.sqrt() != 3.0 || nine.floor() != 9.0 || nine.powi(2) != 81.0) { return 41; }

    // bits
    if (one.toBits() != 4607182418800017408 || f64.fromBits(4611686018427387904).toBits() != two.toBits()) { return 50; }
    o32: f32 = 1.0;
    m32: f32 = -1.0;
    if (o32.toBits() != 1065353216 || m32.toBits() != 3212836864 || f32.fromBits(3212836864) != -1.0) { return 51; }
    if (PI.toBits() != 4614256656552045848) { return 52; }

    // the total order
    v: Vec<f64>;
    v.push(3.0); v.push(NAN); v.push(-z); v.push(z); v.push(-INFINITY); v.push(1.0); v.push(-NAN);
    sortBy(&v, TotalOrder { });
    if (!v.get(0).isNan() || !v.get(0).isSignNegative() || v.get(1) != -INFINITY) { return 60; }
    if (!v.get(2).isSignNegative() || v.get(3).isSignNegative() || v.get(4) != 1.0 || v.get(5) != 3.0 || !v.get(6).isNan()) { return 61; }
    if (one.totalCmp(two) >= 0 || z.totalCmp(-z) <= 0 || NAN.totalCmp(NAN) != 0) { return 62; }

    // Encode / Decode
    s: Sample = Sample { x: -1.5e-300, y: third, n: 7 };
    bytes: Vec<u8> = encodeValue(s);
    if (bytes.len() != 13) { return 70; }
    view: [u8] = "";
    unsafe { view = bytesOf(&bytes); }
    r: Result<Sample, str> = decodeValue(view);
    if (r.isErr()) { return 71; }
    t: Sample = r.unwrap();
    if (t.x != s.x || t.y != s.y || t.n != 7) { return 72; }
    return 0;
}
