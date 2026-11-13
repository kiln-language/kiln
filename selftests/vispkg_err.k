// `shared` is package-private to `vis`, and this file is not in that package.
#include <vis::helpers>
main -> int { return shared() as int; }
