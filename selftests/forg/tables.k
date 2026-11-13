// Globals another module of the package walks with `for x in G` (`walk.k`, `ambiguous_err.k`).
#include <stdlib::vec>

pub struct Pt { x: long, y: long }
pub struct Bag { items: Vec<long> }
pub var gItems: Vec<long> = vec![];
pub var gPts: Vec<Pt> = vec![];
pub var gBag: Bag = Bag { items: vec![] };
pub var gDup: Vec<long> = vec![];

pub fill -> void {
    gItems.push(1); gItems.push(2);
    gPts.push(Pt { x: 3, y: 4 });
    gBag.items.push(10);
    gDup.push(9);
}
