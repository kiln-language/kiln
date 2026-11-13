struct Cell { a: long, b: long }
main -> long {
    cs: [Cell; 3];
    cs[1].a = 5;
    cs[1].b = 9;
    cs[0].a = 1;
    cs[2].b = 2;
    return cs[1].a + cs[1].b + cs[0].a + cs[2].b;
}
