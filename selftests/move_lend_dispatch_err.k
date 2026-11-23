// A dispatch takes what its trait's method marks `sink` and lends the rest.
#include <stdlib::io>
#include <stdlib::vec>
#include <stdlib::string>
var gKeep: Vec<String>;
trait Tr { m2 &self r:String s:sink String -> void; }
struct E { n: long }
methods E for Tr { m2 &self r:String s:String -> void { println("{}", r); gKeep.push(s); } }
go o:Tr -> void { x: String = format("hello"); o.m2(x, x); }
main -> int { e: E = E { n: 1 }; go(e); return 0; }
