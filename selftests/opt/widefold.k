// Literal arithmetic stored in a long folds at the long's width: 2^40, not the 0 an `int` gives
// (which once made the optimizer's scratch slots collide with names: `flow_slot_root`).
// ir-has: widefold::big const 1099511627776
big -> long { x: long = 1 << 40; return x; }
main -> int {
    if (big() != 1099511627776) { return 1; }
    return 0;
}
