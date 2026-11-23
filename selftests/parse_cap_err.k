#include <stdlib::io>

// One error in each of 24 declarations: 20 are reported, then the compile stops.

f1 -> long { return 1 }
f2 -> long { return 2 }
f3 -> long { return 3 }
f4 -> long { return 4 }
f5 -> long { return 5 }
f6 -> long { return 6 }
f7 -> long { return 7 }
f8 -> long { return 8 }
f9 -> long { return 9 }
f10 -> long { return 10 }
f11 -> long { return 11 }
f12 -> long { return 12 }
f13 -> long { return 13 }
f14 -> long { return 14 }
f15 -> long { return 15 }
f16 -> long { return 16 }
f17 -> long { return 17 }
f18 -> long { return 18 }
f19 -> long { return 19 }
f20 -> long { return 20 }
f21 -> long { return 21 }
f22 -> long { return 22 }
f23 -> long { return 23 }
f24 -> long { return 24 }

main -> long { return f1(); }
