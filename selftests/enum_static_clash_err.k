// A method may not share a name with a variant: `SA.Unix(...)` would mean the variant.
enum SA { V4(long), Unix }
methods SA { Unix -> SA { return SA.V4(1); } }
main -> int { return 0; }
