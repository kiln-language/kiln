add a:long b:long -> long { return a + b; }

main -> long {
    x: long = 3;
    y: long = 0;
    while (x > 0) {
        y = y + add(x, 2);
        x = x - 1;
    }
    if (y > 10) { y = y - 1; }
    return y;
}
