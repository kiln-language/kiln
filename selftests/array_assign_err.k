// An array literal assigned to an array names every element.
main -> long {
    idx: [long; 4] = [0, 0, 0, 0];
    idx = [0, 1, 0];
    return idx[0];
}
