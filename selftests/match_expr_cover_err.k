enum Shape { Empty, Circle(long) }
mk -> Shape { return Shape.Empty; }
main -> int { match mk() { Circle(x) { return 1; } } return 0; }
