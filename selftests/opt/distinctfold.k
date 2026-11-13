// A distinct type's operators from `with` inline to the base's instructions: no call is left.
// ir-lacks: distinctfold::step call
type Meters = distinct long with Add, Mul, Eq;
step a:Meters b:Meters -> Meters { return a * b + a; }
main -> int {
    x: Meters = step(3 as Meters, 4 as Meters);
    if (x != 15 as Meters) { return 1; }
    return 0;
}
