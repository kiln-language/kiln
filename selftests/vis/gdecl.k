// Globals at the three levels, and functions of this file that use the private one.
#include <stdlib::vec>
local gHidden: Vec<long> = vec![1, 2, 3];
gPlain: long = 4;
pkg gShared: long = 5;
pub gOpen: long = 6;
pub hiddenLen -> long { return gHidden.len() + gPlain; }
