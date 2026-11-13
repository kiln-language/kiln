enum Shape { Empty, Circle(long) }
mk -> Shape { return Shape.Empty; }
main -> int { match mk() { Square(x) { return 1; } _ { } } return 0; }
