struct V { x: long }
methods V for Frob { frob &self -> long { return self.x; } }
main -> int { v: V = V { x: 3 }; return v.frob() as int; }
