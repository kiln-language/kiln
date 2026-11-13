// `secret` is file-private to helpers.k. Including the file does not make it callable.
#include <helpers>
main -> int { return secret() as int; }
