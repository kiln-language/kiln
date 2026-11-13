// Arithmetic over nothing but integer literals takes the width of the 8-byte integer it is stored
// in, passed as, or meets, as a lone literal does. It was computed as an `int` and wrapped:
// `x: long = 1 << 40` was 0, which is how the optimizer's scratch-slot numbering collided with
// names (`flow_slot_root`).
local A: long = 1 << 40;
local B: u64 = 65536 * 65536;
take x:long -> long { return x; }
main -> int {
    y: long = 1 << 40;
    z: long = 0;
    z = 65536 * 65536 * 2;
    w: long = take(1 << 33);
    q: long = 3;
    r: long = q + (1 << 34);
    s: int = 1 << 4;                       // an int stays an int
    ok: long = 0;
    if (A == 1099511627776) { ok = ok + 1; }
    if (B == (4294967296 as u64)) { ok = ok + 1; }
    if (y == A) { ok = ok + 1; }
    if (z == 8589934592) { ok = ok + 1; }
    if (w == 8589934592) { ok = ok + 1; }
    if (r == 17179869187) { ok = ok + 1; }
    if (s == 16) { ok = ok + 1; }
    return ok as int;
}
