main -> long {
    total: long = 0;
    for i in 0..5 {
        if (i == 2) { continue; }
        total = total + i;
    }
    for j in 10..13 { total = total + j; }
    return total;
}
