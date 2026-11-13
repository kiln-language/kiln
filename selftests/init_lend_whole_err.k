// Lending the whole local before anything is assigned: the callee reads it.
struct P { x: long, y: long }
bump inout p:P -> void { p.x = p.x + 1; }
main -> int {
    p: P;
    bump(&p);
    return p.x as int;
}
