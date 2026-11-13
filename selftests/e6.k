struct Cell { a: long, b: long }

main -> long {
    xs: [long; 8];
    i: long = 0;
    while (i < 8) {
        xs[i] = i * i;
        i = i + 1;
    }
    total: long = 0;
    i = 0;
    while (i < 8) {
        total = total + xs[i];
        i = i + 1;
    }
    cs: [Cell; 3];
    cs[1].a = 5;
    cs[1].b = 9;
    return total - 126 + cs[1].a + cs[1].b;
}
