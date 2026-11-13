// A module that includes nothing implements `Add` and `Drop`: both are core's traits, which are in
// every program whether or not anything includes `stdlib::core`.
pub var gDropped: long = 0;
pub struct V { x: long }
methods V for Add<V> { add self o:V -> V { return V { x: self.x + o.x }; } }
pub struct Res { n: long }
methods Res for Drop { drop &self -> void { gDropped = gDropped + self.n; } }
pub sumV a:V b:V -> long { c: V = a + b; return c.x; }
