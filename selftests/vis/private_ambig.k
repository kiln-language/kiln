// Another file's `local` function takes no part in resolving a name: `twice` here is priv_b's,
// though priv_a's private one is in reach too (it was "'twice' is ambiguous"), and priv_a's own
// calls still reach its own. 10 + 20 = 30.
#include <{priv_a, priv_b}>
main -> int { return (twice(5) + viaA(1)) as int; }
