trait Show { show &self -> long; }
struct V { x: long }
methods V for Show { show &self -> long { return 1; } }
methods V for Show { show &self -> long { return 2; } }
main -> int { return 0; }
