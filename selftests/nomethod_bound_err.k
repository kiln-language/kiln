// A method of a generic type declared in a block whose bound the instance does not meet:
// refused at the call, saying which bound, rather than in the emitter by its mangled name.
#include <stdlib::string>
#include <stdlib::vec>
addAll inout v:Vec<String> xs:...String -> void { v.extendSlice(xs); }
main -> int { v: Vec<String>; addAll(&v, stringOf("x")); return v.len() as int; }
