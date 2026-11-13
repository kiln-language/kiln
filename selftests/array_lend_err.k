// `swapValues(&a, &b)` over two arrays: a type parameter cannot stand for an array, and swapping
// the slices `&a[..]` would leave the arrays as they were.
#include <stdlib::mem>
main -> int {
    a: [long; 4];
    b: [long; 4];
    swapValues(&a, &b);
    return 0;
}
