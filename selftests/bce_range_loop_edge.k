// `while (k < 8) { k = k + 1; }` leaves k at 8: its range is [0, 8], one past the array.
var gS: long = 3;
pick s:long -> long {
    a: [long; 8];
    for i in 0..8 { a[i] = i; }
    k: long = 0;
    if (s > 0) { k = s; }
    while (k < 8) { k = k + 1; }
    return a[k];
}
main -> int { return pick(gS) as int; }
