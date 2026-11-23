// A `hold()` that keeps a pointer into what it is lent is declared `unsafe`, as every function
// that keeps a borrow must be. `with` still calls it from safe code: the guard it returns lives
// exactly for the block, inside the borrow, and is released once at its end.
var gDrops: long = 0;
struct Cell { v: long }
struct Guard { at: *Cell }
methods Guard for Drop {
    drop &self -> void {
        unsafe { (*self.at).v = (*self.at).v + 1; }
        gDrops = gDrops + 1;
    }
}
methods Cell { unsafe hold &self -> Guard { return Guard { at: &self as *Cell }; } }
main -> int {
    c: Cell = Cell { v: 40 };
    with c { gDrops = gDrops + 0; }
    with c { gDrops = gDrops + 0; }
    if (gDrops != 2) { return 1; }
    return c.v as int;
}
