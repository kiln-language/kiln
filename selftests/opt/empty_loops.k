// A loop that does nothing anyone sees is no loop (`Opt.dropEmptyLoops`): `Vec<long>.truncate`'s
// drop loop over elements whose drop does nothing. A branch to the next instruction, left by an
// `if` whose arm did nothing, goes too, and with it the load it tested. These stay: a loop with
// a store in it, one whose counter is read after it, one whose sum is, one that may never end
// (`i <= n` with n the largest long) and one whose counter steps other than by adding one.
// ir-lacks: empty_loops::cut jmp
// ir-lacks: empty_loops::scan jmp
// ir-has: empty_loops::kept jmp
// ir-has: empty_loops::after jmp
// ir-has: empty_loops::total jmp
// ir-has: empty_loops::upto jmp
// ir-has: empty_loops::flip jmp
#include <stdlib::vec>
var gS: long = 0;
cut v:&Vec<long> n:long -> void { v.truncate(n); }
scan v:&Vec<u8> -> void {
    for i in 0..v.len() { b: u8 = v[i]; if (b < 128) { } }
}
kept n:long -> void { for i in 0..n { gS = gS + i; } }
after n:long -> long {
    i: long = 0;
    while (i < n) { i = i + 1; }
    return i;
}
total n:long -> long {
    s: long = 0;
    for i in 0..n { s = s + i; }
    return s;
}
upto n:long -> void {
    i: long = 0;
    while (i <= n) { i = i + 1; }
}
flip k:long n:long -> void {
    i: long = k;
    while (i < n) { i = i ^ 1; }
}
main -> int {
    v: Vec<long>;
    for i in 0..10 { v.push(i); }
    cut(&v, 4);
    if (v.len() != 4 || v[3] != 3) { return 1; }
    w: Vec<u8>;
    for i in 0..300 { w.push(i as u8); }
    scan(&w);
    kept(5);
    if (gS != 10) { return 2; }
    if (after(7) != 7) { return 3; }
    if (total(5) != 10) { return 4; }
    upto(6);
    flip(0, 1);
    return 0;
}
