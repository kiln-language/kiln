enum Shape { Empty, Circle(long) }
mk -> Shape { return Shape.Empty; }
main -> int { match mk() { Circle(x, y) { return 1; } _ { } } return 0; }
