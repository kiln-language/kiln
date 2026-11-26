// A sum an access reads through a conversion between the kinds an address travels as is the
// access's to fold (`Scaler.fold`), not a `lea` of its own (`Scaler.foldArith`): `*((p + i * 4) as
// *u32)` is one load from `[p + i*4]`. Made a `lea` first, it left the load a register of its own.
// ir-lacks: lea_access::sum4 lea [
sum4 p:long n:long -> u64 {
    s: u64 = 0;
    unsafe { for i in 0..n { s += *((p + i * 4) as *u32) as u64; } }
    return s;
}
main -> int {
    a: [u32; 6] = [1, 2, 3, 4, 5, 6];
    p: long = 0;
    unsafe { p = &a[0] as long; }
    if (sum4(p, 6) != 21 || sum4(p, 3) != 6) { return 1; }
    return 0;
}
