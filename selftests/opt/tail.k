// A call to itself in return position is a jump: ten million levels deep, and no stack.
// ir-lacks: tail::down call tail::down
// ir-lacks: tail::gcd call tail::gcd
down n:long acc:long -> long { if (n == 0) { return acc; } return down(n - 1, acc + 2); }
gcd a:long b:long -> long { if (b == 0) { return a; } return gcd(b, a % b); }
main -> int {
    if (down(10000000, 0) != 20000000 || gcd(1071, 462) != 21) { return 1; }
    return 0;
}
