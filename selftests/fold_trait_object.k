// A global holding a trait object, folded at compile time: the object's data pointer relocates
// to the global it borrows, its vtable word to the table's label (docs/comptime.md, step 3).
// The C++ seed refuses this program (under its rules, a trait object stored in a global is a
// borrow that can outlive its referent), so it lives here, where only this compiler runs it.
// The exit code is the two areas summed: 75 + 16.
struct Circle { r: long }
struct Square { side: long }
trait Shape { area self -> long; }
methods Circle for Shape { area self -> long { return self.r * self.r * 3; } }
methods Square for Shape { area self -> long { return self.side * self.side; } }
struct Named { label: str, shape: Shape }

C: Circle = Circle { r: 5 };
S: Shape = C;                                   // data -> gbl_C, vtable -> vt_Circle_Shape
Q: Square = Square { side: 4 };
N: Named = Named { label: "boxed", shape: Q };  // the same, one field in

main -> int { return (S.area() + N.shape.area()) as int; }
