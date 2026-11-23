// A tuple's fields are its element numbers; the note lists them.
main -> int { t: (long, str) = (1, "x"); n: long = t.2; return n as int; }
