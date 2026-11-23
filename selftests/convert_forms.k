// Every integer conversion where the source's form and the target's differ: a widening that
// changes signedness, a narrowing, a change of signedness at one width. Each goes through a fn
// value so it runs, not folds, and its result is read back as a `long`.
i8u16 x:i8 -> u16 { return x as u16; }
i8u32 x:i8 -> u32 { return x as u32; }
i16u32 x:i16 -> u32 { return x as u32; }
intu16 x:int -> u16 { return x as u16; }
u8i8 x:u8 -> i8 { return x as i8; }
u8int x:u8 -> int { return x as int; }
u16i16 x:u16 -> i16 { return x as i16; }
u16int x:u16 -> int { return x as int; }
longu8 x:long -> u8 { return x as u8; }
longu32 x:long -> u32 { return x as u32; }
u32int x:u32 -> int { return x as int; }
u32long x:u32 -> long { return x as long; }
intlong x:int -> long { return x as long; }
i8i16 x:i8 -> i16 { return x as i16; }
longi8 x:long -> i8 { return x as i8; }

main -> int {
    a: fn(i8) -> u16 = &i8u16; b: fn(i8) -> u32 = &i8u32; c: fn(i16) -> u32 = &i16u32;
    d: fn(int) -> u16 = &intu16; e: fn(u8) -> i8 = &u8i8; f: fn(u8) -> int = &u8int;
    g: fn(u16) -> i16 = &u16i16; h: fn(u16) -> int = &u16int; k: fn(long) -> u8 = &longu8;
    m: fn(long) -> u32 = &longu32; n: fn(u32) -> int = &u32int; q: fn(u32) -> long = &u32long;
    r: fn(int) -> long = &intlong; s: fn(i8) -> i16 = &i8i16; t: fn(long) -> i8 = &longi8;
    if (a(-1) as long != 65535) { return 1; }
    if (b(-1) as long != 4294967295) { return 2; }
    if (c(-2) as long != 4294967294) { return 3; }
    if (d(-5) as long != 65531) { return 4; }
    if (e(200) as long != -56) { return 5; }
    if (f(200) as long != 200) { return 6; }
    if (g(60000) as long != -5536) { return 7; }
    if (h(60000) as long != 60000) { return 8; }
    if (k(300) as long != 44) { return 9; }
    if (m(-1) as long != 4294967295) { return 10; }
    if (n(4294967295) as long != -1) { return 11; }
    if (q(4294967295) != 4294967295) { return 12; }
    if (r(-1) != -1) { return 13; }
    if (s(-128) as long != -128) { return 14; }
    if (t(383) as long != 127 || t(129) as long != -127) { return 15; }
    return 0;
}
