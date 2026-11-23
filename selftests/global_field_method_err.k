// A method of the global that writes the walked field through `self` is refused, as one that
// names the global is.
#include <stdlib::vec>
struct Reg { items: Vec<long>, count: long }
var gReg: Reg = Reg { items: vec![1, 2], count: 0 };
methods Reg {
    refill &self -> void { self.items.push(3); self.count = self.count + 1; }
}
step -> void { gReg.refill(); }
main -> int {
    t: long = 0;
    for x in gReg.items { step(); t = t + x; }
    return t as int;
}
