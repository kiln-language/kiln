// A backed enum's variant may be negative (`Again = -11`), and counting on goes from it; a u64
// one may use the whole range. 11 + 22 + 1 + 1 (Less) + 2 (match) + 8 (Top) = 45.
enum Errno: int { Again = -11, Inval = -22, Ok = 0, Next }
enum Ordering: int { Less = -1, Equal, Greater }
enum Big: u64 { Top = 0xFFFF_FFFF_FFFF_FFFF, Mid = 9_223_372_036_854_775_808 }
main -> int {
    e: Errno = Errno.Again;
    t: long = 0 - (e as long) - (Errno.Inval as long) + (Errno.Next as long);
    if (Ordering.Less as int < 0 && Ordering.Greater as int == 1) { t = t + 1; }
    match e { Again { t = t + 2; } Inval { t = t + 100; } _ { t = t + 200; } }
    if ((Big.Top as u64) == 18446744073709551615 && (Big.Mid as u64) > (Big.Top as u64) / (2 as u64)) { t = t + 8; }
    return t as int;
}
