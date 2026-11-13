var counter: long = 10;
var step: long = 4;

bump -> long {
    counter = counter + step;
    return counter;
}

main -> long {
    bump();
    bump();
    return counter - 15;
}
