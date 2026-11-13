main -> long {
    xs: [long; 8];
    i: long = 0;
    while (i < 8) { xs[i] = i * i; i = i + 1; }
    total: long = 0;
    i = 0;
    while (i < 8) { total = total + xs[i]; i = i + 1; }
    return total - 100;
}
