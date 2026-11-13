// f64 and f32: literals, arithmetic, negation, comparisons with NaN, infinities, -0.0, and the
// conversions both ways. Each check is a bit of the exit code; 0 is all of them right. The bits
// are read through `asm`, which hands a float over as the integer register it is in.
bits x:f64 -> long { r: long = 0; unsafe { asm { in rax x; out r rax; } } return r; }
bits32 x:f32 -> long { r: long = 0; unsafe { asm { in rax x; out r rax; } } return r & 4294967295; }
// Through parameters, so the arithmetic happens at run time and not in the constant folder.
add a:f64 b:f64 -> f64 { return a + b; }
sub a:f64 b:f64 -> f64 { return a - b; }
mul a:f64 b:f64 -> f64 { return a * b; }
div a:f64 b:f64 -> f64 { return a / b; }
neg a:f64 -> f64 { return -a; }
lt a:f64 b:f64 -> bool { return a < b; }
eq a:f64 b:f64 -> bool { return a == b; }
ne a:f64 b:f64 -> bool { return a != b; }
ge a:f64 b:f64 -> bool { return a >= b; }
addf a:f32 b:f32 -> f32 { return a + b; }
toLong x:f64 -> long { return x as long; }
toU64 x:f64 -> u64 { return x as u64; }
fromLong n:long -> f64 { return n as f64; }
fromU64 n:u64 -> f64 { return n as f64; }
widen x:f32 -> f64 { return x as f64; }
narrow x:f64 -> f32 { return x as f32; }
main -> int {
    bad: long = 0;
    if (bits(add(1.5, 2.25)) != 4615626668101337088) { bad = bad | 1; }          // 3.75
    if (bits(add(0.1, 0.2)) != 4599075939470750516) { bad = bad | 2; }           // 0.30000000000000004
    if (bits(sub(1.5, 2.25)) != -4618441417868443648 || bits(mul(1.5, 2.25)) != 4614782243171205120
        || bits(div(2.0, 3.0)) != 4604180019048437077) { bad = bad | 4; }
    z: f64 = sub(1.0, 1.0);
    if (bits(neg(z)) != bits(-0.0) || bits(-0.0) != 0 - 9223372036854775807 - 1 || bits(neg(-0.0)) != 0) { bad = bad | 8; }
    nan: f64 = div(z, z);
    if (eq(nan, nan) || !ne(nan, nan) || lt(nan, 1.0) || ge(nan, 1.0) || lt(1.0, nan)) { bad = bad | 16; }
    if (nan == nan) { bad = bad | 32; }
    if (!(nan != nan)) { bad = bad | 64; }
    inf: f64 = div(1.0, z);
    if (bits(inf) != 9218868437227405312 || !lt(1.0e308, inf) || bits(neg(inf)) != -4503599627370496) { bad = bad | 128; }
    if (toLong(2.7) != 2 || toLong(-2.7) != -2 || toLong(nan) != 0 - 9223372036854775807 - 1) { bad = bad | 256; }
    if (bits(fromLong(10000000000)) != 4756540486875873280 || bits(fromU64((0 - 1) as u64)) != 4895412794951729152) { bad = bad | 512; }
    if (toU64(1.8446744073709550e19) != (0 - 2048) as u64 || toU64(3.9) != 3 as u64) { bad = bad | 1024; }
    if (bits32(addf(1.5, 1.75)) != 1080033280) { bad = bad | 2048; }               // 3.25f
    if (bits(widen(0.1)) != bits(0.10000000149011612)) { bad = bad | 4096; }       // the f32 nearest 0.1, widened
    if (bits32(narrow(0.1)) != 1036831949) { bad = bad | 8192; }                    // 0x3DCCCCCD
    if (bits(1e-3) != 4562254508917369340 || bits(2.0e10) != 4761340124128346112 || bits(4.9e-324) != 1) { bad = bad | 16384; }
    if (!eq(-0.0, 0.0) || ne(-0.0, 0.0)) { bad = bad | 32768; }                     // -0.0 == 0.0
    return bad as int;
}
