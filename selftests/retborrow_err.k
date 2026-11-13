// A borrow of this frame's own local dangles the moment the frame ends.
struct Res { id: long }
bad -> &Res { r: Res = Res { id: 1 }; return r; }
main -> int { return 0; }
