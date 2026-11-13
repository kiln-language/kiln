// Two modules each declare a `pub spell`; a call resolves through the CALLING module's includes,
// so `usea` reaches a's and `useb` reaches b's -- not whichever was registered last under the
// bare spelling. Exit code 11.
#include <usea>
#include <useb>
main -> int { return (fromA() + fromB()) as int; }
