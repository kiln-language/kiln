// An `any` box is read through formatting, not by its words.
take xs:...any -> long { return xs[0].tag; }
main -> int { return take(1, 2) as int; }
