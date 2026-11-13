struct P { x: long }
mk -> P { return P { x: 0 }; }
main -> int { mk().x += 1; return 0; }
