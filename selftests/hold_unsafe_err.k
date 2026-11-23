// Outside `with`, a `hold()` declared `unsafe` is called as any unsafe function is: only from
// unsafe code. The trust `with` gives it belongs to the call `with` makes.
struct Cell { v: long }
struct Guard { at: *Cell }
methods Guard for Drop { drop &self -> void { } }
methods Cell { unsafe hold &self -> Guard { return Guard { at: &self as *Cell }; } }
main -> int {
    c: Cell = Cell { v: 41 };
    g: Guard = c.hold();
    return 0;
}
