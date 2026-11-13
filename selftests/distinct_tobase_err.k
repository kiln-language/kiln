// A distinct type converts only by `as`, and has no operator it does not implement.
type Meters = distinct long;
type Feet = distinct long;
takesM m:Meters -> long { return m as long; }
main -> int { m: Meters = 5 as Meters; x: long = m; return x as int; }
