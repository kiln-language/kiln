// Indexing reads and writes one element at the element's own width, for every width: a `str`
// is bytes (`s[i]` is a bounds-checked u8, `s[a..b]` a str), `[u8]`, `[u16]`, `[i16]`, `[int]`,
// `[u32]`, `[long]`, `[bool]`, `[char]`, `[double]`, `[str]` and slices of structs of several
// sizes, as locals, fields, slices of slices and `inout` slices; and the evaluator agrees.
struct P3 { a: u8, b: u8, c: u8 }
struct P12 { x: int, y: long }
struct P24 { x: long, y: long, z: long }
struct Holder { b: [u16; 4], s: str }

sumU8 xs:[u8] -> long { t: long = 0; for i in 0..xs.len { t = t + (xs[i] as long); } return t; }
sumU16 xs:[u16] -> long { t: long = 0; for i in 0..xs.len { t = t + (xs[i] as long); } return t; }
sumI16 xs:[i16] -> long { t: long = 0; for i in 0..xs.len { t = t + (xs[i] as long); } return t; }
sumInt xs:[int] -> long { t: long = 0; for i in 0..xs.len { t = t + (xs[i] as long); } return t; }
sumU32 xs:[u32] -> long { t: long = 0; for i in 0..xs.len { t = t + (xs[i] as long); } return t; }
sumLong xs:[long] -> long { t: long = 0; for i in 0..xs.len { t = t + xs[i]; } return t; }
sumP3 xs:[P3] -> long { t: long = 0; for i in 0..xs.len { t = t + (xs[i].c as long); } return t; }
sumP12 xs:[P12] -> long { t: long = 0; for i in 0..xs.len { t = t + (xs[i].x as long) + xs[i].y; } return t; }
sumP24 xs:[P24] -> long { t: long = 0; for i in 0..xs.len { t = t + xs[i].z; } return t; }
fillU16 inout xs:[u16] v:u16 -> void { for i in 0..xs.len { xs[i] = v; } }
fillInt inout xs:[int] v:int -> void { for i in 0..xs.len { xs[i] = v; } }
fillU8 inout xs:[u8] v:u8 -> void { for i in 0..xs.len { xs[i] = v; } }
strSum s:str -> long { t: long = 0; for i in 0..s.len { t = t + (s[i] as long); } return t; }

// Folded at compile time: the evaluator's reading of the same expressions.
FOLD_S: str = "kiln";
FOLD_B: long = (FOLD_S[1] as long) + (FOLD_S[3] as long) * 1000 + FOLD_S[1..3].len * 1000000;
foldWide -> long {
    w: [u16; 3]; w[0] = 1; w[1] = 300; w[2] = 65535;
    i: [int; 3]; i[0] = -1; i[1] = 7; i[2] = 100000;
    return sumU16(w[..]) * 10 + sumInt(i[1..]);
}
FOLD_W: long = foldWide();

main -> int {
    bad: long = 0;
    s: str = "abcdefghijklmnopqrstuvwxyz";
    if (s[0] != 97 || s[1] != 98 || s[25] != 122) { bad = bad + 1; }
    if ((s[2] as long) + 1 != 100) { bad = bad + 1; }
    t: str = s[1..4];
    if (t.len != 3 || t[0] != 98 || t[2] != 100) { bad = bad + 1; }
    u: str = s[23..];
    if (u.len != 3 || u[0] != 120) { bad = bad + 1; }
    if (strSum("ab") != 195) { bad = bad + 1; }
    if (s[2..5][1] != 100) { bad = bad + 1; }
    h: Holder = Holder { s: "xyz" };
    h.b[1] = 513; h.b[3] = 7;
    if (h.s[1] != 121 || h.b[1] != 513 || h.b[0] != 0 || h.b[3] != 7) { bad = bad + 1; }
    if (sumU16(h.b[..]) != 520) { bad = bad + 1; }

    b: [u8; 5]; for i in 0..5 { b[i] = (i * 60) as u8; }
    if (sumU8(b[..]) != 600 || sumU8(b[1..3]) != 180 || b[4] != 240) { bad = bad + 1; }
    w: [u16; 5]; for i in 0..5 { w[i] = (i * 20000) as u16; }
    if (w[3] != 60000 || sumU16(w[2..]) != 114464 || w[4] != 14464) { bad = bad + 1; }
    k: [i16; 4]; k[0] = -3; k[1] = 30000; k[2] = -30000; k[3] = 5;
    if (k[0] != -3 || sumI16(k[..]) != 2) { bad = bad + 1; }
    n: [int; 4]; n[0] = -1; n[1] = 2000000000; n[2] = 3; n[3] = -4;
    if (n[1] != 2000000000 || sumInt(n[..]) != 1999999998 || sumInt(n[2..4]) != -1) { bad = bad + 1; }
    m: [u32; 3]; m[0] = 4000000000 as u32; m[1] = 1; m[2] = 2;
    if (sumU32(m[..]) != 4000000003) { bad = bad + 1; }
    l: [long; 3]; l[0] = 1 << 40; l[1] = -1; l[2] = 5;
    if (sumLong(l[..]) != (1 << 40) + 4 || l[0] != 1 << 40) { bad = bad + 1; }
    f: [bool; 3]; f[1] = true;
    if (f[0] || !f[1] || f[2]) { bad = bad + 1; }
    c: [char; 3]; c[0] = 'x'; c[1] = 'y'; c[2] = 'z';
    if (c[1] != 'y' || c[2] != 'z') { bad = bad + 1; }
    d: [double; 2]; d[0] = 1.5; d[1] = 2.25;
    if (d[0] + d[1] != 3.75) { bad = bad + 1; }
    ss: [str; 3]; ss[0] = "a"; ss[1] = "bcd"; ss[2] = "ef";
    if (ss[1].len != 3 || ss[1][2] != 100 || ss[..][2][1] != 102) { bad = bad + 1; }
    if (ss[..][2].len != 2 || ss[1..][0].len != 3 || b[1..3][1] != 120 || n[1..][0] != 2000000000) { bad = bad + 1; }

    p3: [P3; 3]; for i in 0..3 { p3[i] = P3 { a: 1, b: 2, c: (i + 10) as u8 }; }
    if (sumP3(p3[..]) != 33 || p3[2].c != 12 || sumP3(p3[1..]) != 23) { bad = bad + 1; }
    p12: [P12; 3]; for i in 0..3 { p12[i] = P12 { x: (i + 1) as int, y: i * 100 }; }
    if (sumP12(p12[..]) != 306 || p12[2].y != 200 || sumP12(p12[1..2]) != 102) { bad = bad + 1; }
    p24: [P24; 3]; for i in 0..3 { p24[i] = P24 { x: 0, y: 0, z: i + 1 }; }
    if (sumP24(p24[..]) != 6 || sumP24(p24[2..]) != 3) { bad = bad + 1; }

    fillU16(&w[1..3], 9);
    if (w[0] != 0 || w[1] != 9 || w[2] != 9 || w[3] != 60000) { bad = bad + 1; }
    fillInt(&n[..2], 6);
    if (n[0] != 6 || n[1] != 6 || n[2] != 3) { bad = bad + 1; }
    fillU8(&b[3..], 1);
    if (b[2] != 120 || b[3] != 1 || b[4] != 1) { bad = bad + 1; }

    if (FOLD_B != 2110105) { bad = bad + 1; }
    if (FOLD_W != 758367) { bad = bad + 1; }
    return bad as int;
}
