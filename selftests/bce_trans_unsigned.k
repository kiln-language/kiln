// A bounds check is unsigned: `i < m` and `m <= 4` (signed) give i < 4 only when i is never
// negative, and here it starts at -1, so the array read keeps its check and panics.
var gM: long = 4;
main -> int {
    a: [long; 4] = [1, 2, 3, 4];
    m: long = gM;
    if (m > 4) { return 0; }
    s: long = 0;
    i: long = -1;
    while (i < m) { s = s + a[i]; i = i + 1; }
    return s as int;
}
