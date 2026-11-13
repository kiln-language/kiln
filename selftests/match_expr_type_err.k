mk -> long { return 3; }
main -> int { match mk() { Some(x) { return 1; } _ { } } return 0; }
