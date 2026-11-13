// An array literal assigned to an array place as a whole: a local, a `var`
// global, a field, a field through a borrow; every element given; values computed before any is
// stored, so one may read the array it replaces; owning elements released once.
#include <stdlib::{string, vec}>
struct Grid { cells: [long; 3], tag: long }
struct Deep { g: Grid }
var gArr: [long; 2] = [1, 2];
setCells g:&Grid -> void { g.cells = [7, 8, 9]; }
main -> long {
    idx: [long; 4] = [0, 0, 0, 0];
    idx = [0, 1, 0, 1];
    if (idx[0] + idx[1] + idx[2] + idx[3] != 2) { return 1; }
    idx = [idx[3] + 5, idx[2], idx[1], idx[0]];       // reads the old values
    if (idx[0] != 6 || idx[1] != 0 || idx[2] != 1 || idx[3] != 0) { return 2; }
    g: Grid = Grid { tag: 4 };
    g.cells = [1, 2, 3];
    g.cells = [g.cells[2], g.cells[1], g.cells[0]];
    if (g.cells[0] != 3 || g.cells[2] != 1 || g.tag != 4) { return 3; }
    setCells(&g);
    if (g.cells[1] != 8) { return 4; }
    d: Deep = Deep { g: Grid { tag: 0 } };
    d.g.cells = [4, 5, 6];
    if (d.g.cells[0] + d.g.cells[1] + d.g.cells[2] != 15) { return 5; }
    gArr = [gArr[1], gArr[0]];
    if (gArr[0] != 2 || gArr[1] != 1) { return 6; }
    names: [String; 2] = [stringOf("a"), stringOf("b")];
    names = [stringOf("cc"), stringOf("ddd")];
    if (names[0].len() + names[1].len() != 5) { return 7; }
    one: [long; 1] = [3];
    one = [one[0] * 2];
    if (one[0] != 6) { return 8; }
    return 42;
}
