// The immutability guard goes on past an error to the next function too: every function's
// first refusal is reported.
local LIMIT: long = 4;
local START: long = 1;
one -> long { LIMIT = 5; return LIMIT; }
two -> long { START = 2; return START; }
three -> long { LIMIT = 6; START = 7; return 0; }
main -> int { return (one() + two() + three()) as int; }
