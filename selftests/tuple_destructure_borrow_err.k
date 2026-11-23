// The names of a tuple taken apart through a reference borrow the vector's element, so the code
// after them may not change the vector: `clear` would release the string `d` points at.
#include <stdlib::vec>
#include <stdlib::string>
main -> int {
    v: Vec<(long, String)>;
    v.push((1, String.new()));
    c, d = v.at(0);
    v.clear();
    return d.len() as int;
}
