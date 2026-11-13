// A generic instance the program never writes down -- `Vec<long>` exists here only because
// `vecOf(1 as long, 2 as long)` returns one -- is stamped by the round that stamps the function,
// and has to be LAID OUT by it too: its `RawVec<long>` field is stamped after it, at no size
// until the relayout. Before that this Vec was eight bytes wide and the temporary holding it
// copied a third of it. Exit code 2.
#include <stdlib::vec>
takeV<T: Copy> v:Vec<T> -> long { return v.len(); }
main -> int { return takeV(vecOf(1 as long, 2 as long)) as int; }
