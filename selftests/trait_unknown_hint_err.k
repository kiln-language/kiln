// A trait the standard library declares in a module of its name, not included.
struct V { x: long }
methods V for Encode { encode &self -> long { return 1; } }
main -> int { return 0; }
