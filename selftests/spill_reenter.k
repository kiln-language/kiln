// A bounds check failing inside the `@spill` function reports without calling it again: the
// report runs once more from inside it and ends the process with 134. Called a second time, this
// spill function would exit 99 instead.
pub unsafe builtin syscall nr:long args:...long -> long;
var gCalls: long = 0;
var gTable: [long; 3];
@spill keep -> void {
    gCalls = gCalls + 1;
    if (gCalls > 1) { unsafe { syscall(60, 99); } }
    s: long = 0;
    for i in 0..gCalls + 3 { s = s + gTable[i]; }
    gTable[0] = s;
}
main -> int {
    a: [long; 4];
    for i in 0..4 { a[i] = i; }
    s: long = 0;
    for i in 0..5 { s = s + a[i]; }
    return s as int;
}
