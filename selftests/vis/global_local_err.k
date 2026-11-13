// `gHidden` is file-private to gdecl.k (declared `local`): including the file does not make it
// readable here.
#include <gdecl>
main -> int { return gHidden.len() as int; }
