// A literal's element type comes from where it is stored (`v: Vec<long> = vec![1, 2, 3]` is
// a Vec<long>), but a Vec whose type is already fixed is not converted: storing a `Vec<int>`
// where a `Vec<long>` was declared is refused, not copied as garbage.
#include <stdlib::vec>
mk -> Vec<int> { return vec![int: 1, 2, 3]; }
main -> int { v: Vec<long> = mk(); return v.len() as int; }
