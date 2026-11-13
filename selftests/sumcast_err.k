// A BACKED enum is its backing integer and casts to one. A SUM type is a tag and a payload;
// casting it to an integer reads the tag by accident. `aggregateType` used to exempt both.
enum Shape { Empty, Circle(long) }
main -> int { s: Shape = Shape.Empty; return (s as long) as int; }
