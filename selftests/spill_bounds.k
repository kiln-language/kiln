// A failed bounds check calls the program's `@spill` function before its report, so what the
// program holds back for stdout is written first. This one's spill function ends the process with
// 70 plus what the program had put by, which the report (exit 134) never would: exit 77 shows the
// report called it, and that it saw the program's state.
pub unsafe builtin syscall nr:long args:...long -> long;
var gHeld: long = 0;
@spill keep -> void { unsafe { syscall(60, 70 + gHeld); } }
main -> int {
    a: [long; 4];
    for i in 0..4 { a[i] = i; }
    gHeld = 7;
    s: long = 0;
    for i in 0..5 { s = s + a[i]; }
    return s as int;
}
