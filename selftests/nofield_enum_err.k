// Neither has a plain enum; the type is named as it is written.
enum Color { Red, Green }
main -> int { c: Color = Color.Green; return c.value as int; }
